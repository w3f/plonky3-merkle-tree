use std::fmt::Debug;
use std::marker::PhantomData;

use rand::{random, Rng, SeedableRng};
use rand::rngs::{StdRng, ThreadRng};
use rand::distributions::Standard;
use rand::prelude::Distribution;

use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{Field, PrimeField};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;

use p3_challenger::{HashChallenger, SerializingChallenger32};
use p3_circle::CirclePcs;
use p3_commit::ExtensionMmcs;
use p3_field::extension::BinomialExtensionField;
use p3_fri::{create_benchmark_fri_config};
use p3_keccak::Keccak256Hash;
use p3_poseidon2::{Poseidon2, GenericPoseidon2LinearLayers};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_mersenne_31::Mersenne31;
use p3_symmetric::{CompressionFunctionFromHasher, SerializingHasher32};
use p3_uni_stark::{prove, verify, StarkConfig};
use tracing_forest::util::LevelFilter;
use tracing_forest::ForestLayer;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Registry};
use p3_poseidon2::{ExternalLayerConstants, ExternalLayerConstructor, InternalLayerConstructor};

//We basically repeat the vectorized poseiden2 air trick here in entirety
use p3_poseidon2_air::{generate_vectorized_trace_rows, Poseidon2Air, Poseidon2Cols};
use p3_poseidon2_air::{RoundConstants, VectorizedPoseidon2Air};

const SECURE_WIDTH : usize = 8; 
const MERKLE_WIDTH : usize = SECURE_WIDTH * 2;

pub(crate) const POSEIDEN_S_BOX_DEGREE: u64 = 5;

pub type Poseidon2Merkle<F: PrimeField> = Poseidon2<
    F,
    ExternalLayerConstants<F, MERKLE_WIDTH>,
    InternalLayerConstructor<F, MERKLE_WIDTH>,
    MERKLE_WIDTH,
    POSEIDEN_S_BOX_DEGREE,
>;

const ZERO_PAD: [u32; SECURE_WIDTH] = [0u32; SECURE_WIDTH];
const TREE_HEIGHT: usize = 16;


pub struct PoseidenMerkleTreeAir<F: Field,
    LinearLayers,
    const POSEIDEN_WIDTH: usize,
    const POSEIDEN_SBOX_DEGREE: u64,
    const POSEIDEN_SBOX_REGISTERS: usize,
    const POSEIDEN_HALF_FULL_ROUNDS: usize,
    const POSEIDEN_PARTIAL_ROUNDS: usize,
    const POSEIDEN_VECTOR_LEN: usize,
>
 {
    pub(crate) poseiden2_air: Poseidon2Air<
        F,
        LinearLayers,
        POSEIDEN_WIDTH,
        POSEIDEN_SBOX_DEGREE,
        POSEIDEN_SBOX_REGISTERS,
        POSEIDEN_HALF_FULL_ROUNDS,
        POSEIDEN_PARTIAL_ROUNDS,
    >,

    pub poseiden_constants: RoundConstants<F, POSEIDEN_WIDTH, POSEIDEN_HALF_FULL_ROUNDS, POSEIDEN_PARTIAL_ROUNDS>,
    pub tree: Vec<[F; SECURE_WIDTH]>,
    pub proof: Vec<[F; SECURE_WIDTH]>,
    pub leaf_index: usize,
    //pub num_steps: usize,
    //pub final_value: u32,
}

impl<F: PrimeField,
    LinearLayers: ,
    const POSEIDEN_WIDTH: usize,
    const POSEIDEN_SBOX_DEGREE: u64,
    const POSEIDEN_SBOX_REGISTERS: usize,
    const POSEIDEN_HALF_FULL_ROUNDS: usize,
    const POSEIDEN_PARTIAL_ROUNDS: usize,
    const POSEIDEN_VECTOR_LEN: usize,
     > PoseidenMerkleTreeAir<
        F,
        LinearLayers,
        POSEIDEN_WIDTH,
        POSEIDEN_SBOX_DEGREE,
        POSEIDEN_SBOX_REGISTERS,
        POSEIDEN_HALF_FULL_ROUNDS,
        POSEIDEN_PARTIAL_ROUNDS,
    POSEIDEN_VECTOR_LEN,
    >
{

    pub fn new(constants: RoundConstants<F, POSEIDEN_WIDTH, POSEIDEN_HALF_FULL_ROUNDS, POSEIDEN_PARTIAL_ROUNDS>, tree: Vec<[F; SECURE_WIDTH]>,  leaf_index: usize,

    ) -> Self {
        
        Self {
            poseiden2_air: Poseidon2Air::new(constants),
            poseiden_constants: constants,
            tree: tree,
            leaf_index: leaf_index,
            proof: vec![],  //TODO: compute the correct proof.

        }
    }

    // pub fn generate_vectorized_trace_rows(
    //     &self,
    //     num_hashes: usize,
    //     extra_capacity_bits: usize,
    // ) -> RowMajorMatrix<F>
    // where
    //     F: PrimeField,
    //     LinearLayers: GenericPoseidon2LinearLayers<F, POSEIDEN_WIDTH>,
    //     Standard: Distribution<[F; POSEIDEN_WIDTH]>,
    // {
    //     let inputs = (0..num_hashes).map(|_| random()).collect::<Vec<_>>();
    //     generate_vectorized_trace_rows::<
    //         F,
    //         LinearLayers,
    //         POSEIDEN_WIDTH,
    //         POSEIDEN_SBOX_DEGREE,
    //         POSEIDEN_SBOX_REGISTERS,
    //         POSEIDEN_HALF_FULL_ROUNDS,
    //         POSEIDEN_PARTIAL_ROUNDS,
    //         POSEIDEN_VECTOR_LEN,
    //     >(inputs, &self.air.constants, extra_capacity_bits)
    // }

    fn height() -> usize {
        TREE_HEIGHT
    }
    
    fn internal_node_no() -> usize {
        //2^31 = 2147483648
        //2147483648;
        //2^16 = 65536
        1 << TREE_HEIGHT
    }
    
    // Root node at index 0.
    // Left child of node at index i is at 2*i + 1.
    // Right child of node at index i is at 2*i + 2.
    // Parent of node at index i is at (i - 1) / 2

    /// return leaf index in the tree vec Leaf tree index = number of internal nodes + leaf-index - 1
    fn index_to_tree_index(index: usize) -> usize {
        2 * index + 1
    }

    /// return the index of the sibling of a node
    fn sibling_index(index: usize) -> usize {
        index -2 * Self::is_right_sibling(Self::index_to_tree_index(index)) + 1 
            
    }
        
    /// return true if it is a 1 sibling otherwise 0
    #[inline]
    fn is_right_sibling(index: usize) -> usize {
        index % 2
    }

    /// given an index of node in the tree vector it returns the index
    /// of its parent
    fn parent_index(index: usize) -> usize {
        (index - 1) / 2
    }

    /// return the index of the left child
    fn left_child(index: usize) -> usize {
       2 * index + 1
    }

    fn right_child(index: usize) -> usize {
       2 * index + 2
    }

    fn generate_merkle_proof_trace(&self, tree: Vec<[F; SECURE_WIDTH]>, leaf_index: usize,
    ) -> RowMajorMatrix<F> where
            LinearLayers: GenericPoseidon2LinearLayers<F, POSEIDEN_WIDTH>,
    {

        //We put all rows with all their columns in a flat vector and then we'll
        //tell plonky to turn it into a nice a table with number of columns
        //There are two columns in our air table and the number of steps is the
        //depth of the tree. 
        let mut values = Vec::with_capacity(TREE_HEIGHT * (2 + POSEIDEN_VECTOR_LEN));

        //we can just fill up the columns from the tree
        let current_node = Self::index_to_tree_index(leaf_index);

        //not clear what are these for
        let extra_capacity_bits = 0;
    
        for _ in 0..TREE_HEIGHT {
            (0..SECURE_WIDTH).map(|i| values.push(self.tree[current_node][i]));
            (0..SECURE_WIDTH).map(|i| values.push(self.tree[Self::sibling_index(current_node)][i]));

            let concat_input: [F; POSEIDEN_WIDTH];
                concat_input[..SECURE_WIDTH].copy_from_slice(&self.tree[current_node]);
                concat_input[SECURE_WIDTH..].copy_from_slice(&self.tree[Self::sibling_index(current_node)]);
            let inputs = vec![concat_input];
            let poseiden_matrix = generate_vectorized_trace_rows::<
                    F,
                LinearLayers,
                POSEIDEN_WIDTH,
                POSEIDEN_SBOX_DEGREE,
                POSEIDEN_SBOX_REGISTERS,
                POSEIDEN_HALF_FULL_ROUNDS,
                POSEIDEN_PARTIAL_ROUNDS,
                POSEIDEN_VECTOR_LEN,
                >(inputs, &self.poseiden_constants, extra_capacity_bits);
            current_node = Self::parent_index(current_node);
            
            //this supposed to be a one row matrix
            for j in (0..POSEIDEN_VECTOR_LEN).step_by(SECURE_WIDTH) {
                
                values.push(poseiden_matrix.get(0, j))
            }
            
        }
        RowMajorMatrix::new(values, 2 + POSEIDEN_VECTOR_LEN)
    }
        
}

////
//
//  |   | path          | co-path                                   |
//  |---+---------------+-------------------------------------------|
//  | 0 | Hash(Leaf)    | Hash(co-leaf) = Merkle Value of Neighbour |
//  | 1 | Hash(0,0-0,1) | Merkle value co-node of parent            |
//  | 2 | Hash(1,0-1,1) |                                           |
//  | 3 |               |                                           |
//  | 4 |               |                                           |
impl<
        F: Field,
        LinearLayers: Sync,
        const POSEIDEN_WIDTH: usize,
        const POSEIDEN_SBOX_DEGREE: u64,
        const POSEIDEN_SBOX_REGISTERS: usize,
        const POSEIDEN_HALF_FULL_ROUNDS: usize,
        const POSEIDEN_PARTIAL_ROUNDS: usize,
        const POSEIDEN_VECTOR_LEN: usize,
    > BaseAir<F>
    for PoseidenMerkleTreeAir<
        F,
        LinearLayers,
        POSEIDEN_WIDTH,
        POSEIDEN_SBOX_DEGREE,
        POSEIDEN_SBOX_REGISTERS,
        POSEIDEN_HALF_FULL_ROUNDS,
        POSEIDEN_PARTIAL_ROUNDS,
        POSEIDEN_VECTOR_LEN,
        >
{
    fn width(&self) -> usize {
        2 +  self.poseiden2_air.width() * POSEIDEN_VECTOR_LEN
// It will be hash of a node and its sibling plus as many column we need for Poseiden
    }
}

impl<
        AB: AirBuilder,
    LinearLayers: GenericPoseidon2LinearLayers<AB::Expr, POSEIDEN_WIDTH>,
    const POSEIDEN_WIDTH: usize,
    const POSEIDEN_SBOX_DEGREE: u64,
    const POSEIDEN_SBOX_REGISTERS: usize,
    const POSEIDEN_HALF_FULL_ROUNDS: usize,
    const POSEIDEN_PARTIAL_ROUNDS: usize,
    const POSEIDEN_VECTOR_LEN: usize,
    > Air<AB> for PoseidenMerkleTreeAir 
    <
            AB::F,
        LinearLayers,
        POSEIDEN_WIDTH,
        POSEIDEN_SBOX_DEGREE,
        POSEIDEN_SBOX_REGISTERS,
        POSEIDEN_HALF_FULL_ROUNDS,
        POSEIDEN_PARTIAL_ROUNDS,
        POSEIDEN_VECTOR_LEN,
>
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);         //we are climbing up the tree
        let next = main.row_slice(1);
        // Enforce starting values: make sure they are equal to the leaves
        // First we should know if we are right or left leave. even = left, odd = right
        // let neighbour_index = match(leaf_index % 2) {
        //     0 => leaf_index + 1,
        //     1 => leaf_index - 1,
        // };

        //let poseiden2 = Poseidon2Merkle::<AB::F>;

        //First row is dealing with hash of leaves
        builder.when_first_row().assert_eq(local[0], //poseidon2.permute(            //            [
                AB::Expr::from_canonical_u32(self.tree[
                self.index_to_tree_index(
                    self.leaf_index)]),
             
//                ZERO_PAD
//            ]
//        )[0..SECURE_WIDTH]
        );

        //Assuming the leafs are already hash of something
        builder.when_first_row().assert_eq(local[1], //poseidon2.permute(            
//            [
                AB::Expr::from_canonical_u32(self.tree[
                self.sibling_index(self.index_to_tree_index(
                    self.leaf_index))]),
             
        //         ZERO_PAD
        //     ]
        // )[0..SECURE_WIDTH]
        ); //Probably redundant (column 1 is input)

        //we verify that poseiden2 is evaluated correctly
        for perm in &local.cols[2..] {
            eval(&self.air, builder, perm);
        }

        // Enforce state transition constraintse
        // next is parent, it should be equal hash of childs
        builder.when_transition().assert_eq(next[0], 

                local.cols[-1],
        );        
        //builder.when_tansition().assert_eq(next[1], local[0] + local[1]);

        // Constrain the final value
        let merkle_root = self.tree[0];
        let final_value = AB::Expr::from_canonical_u32(merkle_root);
        builder.when_last_row().assert_eq(local[1], final_value);
    }

}

const POSEIDEN_WIDTH: usize = 16;
const POSEIDEN_SBOX_DEGREE: u64 = 7;
const POSEIDEN_SBOX_REGISTERS: usize = 1;
const POSEIDEN_HALF_FULL_ROUNDS: usize = 4;
const POSEIDEN_PARTIAL_ROUNDS: usize = 20;
const POSEIDEN_VECTOR_LEN: usize = 1 << 3;

fn main() -> Result<(), impl Debug> {
    let env_filter = EnvFilter::builder()
        .with_default_directive(LevelFilter::INFO.into())
        .from_env_lossy();
    Registry::default()
        .with(env_filter)
        .with(ForestLayer::default())
        .init();

    type Val = Mersenne31;
    type Challenge = BinomialExtensionField<Val, 3>;

    type ByteHash = Keccak256Hash;
    type FieldHash = SerializingHasher32<ByteHash>;
    let byte_hash = ByteHash {};
    let field_hash = FieldHash::new(Keccak256Hash {});

    type MyCompress = CompressionFunctionFromHasher<ByteHash, 2, 32>;
    let compress = MyCompress::new(byte_hash);

    type ValMmcs = MerkleTreeMmcs<Val, u8, FieldHash, MyCompress, 32>;
    let val_mmcs = ValMmcs::new(field_hash, compress);

    type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
    let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());

    type Challenger = SerializingChallenger32<Val, HashChallenger<u8, ByteHash, 32>>;

    let fri_config = create_benchmark_fri_config(challenge_mmcs);

    // FriConfig {
    //     log_blowup: 1,
    //     num_queries: 100,
    //     proof_of_work_bits: 16,
    //     mmcs: challenge_mmcs,
    // };

    type Pcs = CirclePcs<Val, ValMmcs, ChallengeMmcs>;
    let pcs = Pcs {
        mmcs: val_mmcs,
        fri_config,
        _phantom: PhantomData,
    };

    type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;
    let config = MyConfig::new(pcs);

    let tree_size = 1 << TREE_HEIGHT;
    //TOOD: I'm just going to fill everything randomly just to let the thing compiles
    //Then poseidenize it after
    let tree  = generate_random_tree(tree_size);
    
    let leaf_index : usize = 1;
    let mut rng = rand::thread_rng();

    let constants = RoundConstants::<Val, POSEIDEN_WIDTH, POSEIDEN_HALF_FULL_ROUNDS, POSEIDEN_PARTIAL_ROUNDS>::from_rng(&mut rng);

    let air = PoseidenMerkleTreeAir::new(constants, tree,  leaf_index);
    let trace = air.generate_merkle_proof_trace(tree, leaf_index);

    let mut challenger = Challenger::from_hasher(vec![], byte_hash);
    let proof = prove(&config, &air, &mut challenger, trace, &vec![]);

    let mut challenger = Challenger::from_hasher(vec![], byte_hash);
    verify(&config, &air, &mut challenger, &proof, &vec![])
}

fn generate_random_tree<F: PrimeField>(tree_size: usize) -> Vec<[F; SECURE_WIDTH]> where
    Standard: Distribution<[PrimeField; SECURE_WIDTH]>,
{
    (0..tree_size).map(|_| random()).collect::<Vec<_>>()
    
}
