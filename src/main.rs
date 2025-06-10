use std::fmt::Debug;
use std::marker::PhantomData;
//use rand::rngs::SmallRng;
use rand::distr::StandardUniform;
use rand::prelude::Distribution;

use rand::rngs::{SmallRng, StdRng};
use rand::Rng;
use rand::{random, SeedableRng};

use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{Field, InjectiveMonomial, PrimeCharacteristicRing, PrimeField};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use std::borrow::Borrow;

use p3_challenger::{HashChallenger, SerializingChallenger32};
use p3_circle::CirclePcs;
use p3_commit::ExtensionMmcs;
use p3_field::extension::BinomialExtensionField;
use p3_fri::create_benchmark_fri_config;
use p3_keccak::Keccak256Hash;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_mersenne_31::{
    GenericPoseidon2LinearLayersMersenne31, Mersenne31, Poseidon2ExternalLayerMersenne31,
    Poseidon2InternalLayerMersenne31,
};
use p3_poseidon2::{GenericPoseidon2LinearLayers, Poseidon2};
use p3_symmetric::{CompressionFunctionFromHasher, Permutation, SerializingHasher32};
use p3_uni_stark::{prove, verify, StarkConfig};
use tracing_forest::util::LevelFilter;
use tracing_forest::ForestLayer;
use tracing_subscriber::layer::SubscriberExt;
use tracing_subscriber::util::SubscriberInitExt;
use tracing_subscriber::{EnvFilter, Registry};
//use p3_poseidon2::{ExternalLayerConstants, ExternalLayerConstructor, InternalLayerConstructor};

//We basically repeat the vectorized poseidon2 air trick here in entirety
use p3_poseidon2_air::{air_eval, RoundConstants, VectorizedPoseidon2Cols};
use p3_poseidon2_air::{generate_vectorized_trace_rows, Poseidon2Air};

use p3_poseidon2::{
    ExternalLayer, ExternalLayerConstants, ExternalLayerConstructor, InternalLayer,
    InternalLayerConstructor,
};

const SECURE_WIDTH: usize = 8; //this should be half of posiden width so we could compute
                               // the hash of concatination of two hashes.

const TREE_HEIGHT: usize = 16;

pub struct PoseidonMerkleTreeAir<
    F: Field + InjectiveMonomial<POSEIDON_SBOX_DEGREE>,
    LinearLayers,
    Poseidon2ExternalLayerConstructor: ExternalLayerConstructor<F, POSEIDON_WIDTH>
        + ExternalLayer<F, POSEIDON_WIDTH, POSEIDON_SBOX_DEGREE>,
    Poseidon2InternalLayerConstructor: InternalLayerConstructor<F> + InternalLayer<F, POSEIDON_WIDTH, POSEIDON_SBOX_DEGREE>,
    const POSEIDON_WIDTH: usize,
    const POSEIDON_SBOX_DEGREE: u64,
    const POSEIDON_SBOX_REGISTERS: usize,
    const POSEIDON_HALF_FULL_ROUNDS: usize,
    const POSEIDON_PARTIAL_ROUNDS: usize,
    const POSEIDON_VECTOR_LEN: usize,
> {
    pub(crate) poseidon2_air: Poseidon2Air<
        F,
        LinearLayers,
        POSEIDON_WIDTH,
        POSEIDON_SBOX_DEGREE,
        POSEIDON_SBOX_REGISTERS,
        POSEIDON_HALF_FULL_ROUNDS,
        POSEIDON_PARTIAL_ROUNDS,
    >,

    pub poseidon_beginning_full_round_constants: [[F; POSEIDON_WIDTH]; POSEIDON_HALF_FULL_ROUNDS],
    pub poseidon_partial_round_constants: [F; POSEIDON_PARTIAL_ROUNDS],
    pub poseidon_ending_full_round_constants: [[F; POSEIDON_WIDTH]; POSEIDON_HALF_FULL_ROUNDS],

    pub poseidon_constants:
        RoundConstants<F, POSEIDON_WIDTH, POSEIDON_HALF_FULL_ROUNDS, POSEIDON_PARTIAL_ROUNDS>,
    pub tree: Vec<[F; SECURE_WIDTH]>,
    pub proof: Vec<[F; SECURE_WIDTH]>,
    pub leaf_index: usize,
    pub poseidon2_hasher: Poseidon2<
        F,
        Poseidon2ExternalLayerConstructor,
        Poseidon2InternalLayerConstructor,
        POSEIDON_WIDTH,
        POSEIDON_SBOX_DEGREE,
    >,
}

impl<
        F: PrimeField + InjectiveMonomial<POSEIDON_SBOX_DEGREE>,
        LinearLayers,
        Poseidon2ExternalLayerConstructor: ExternalLayerConstructor<F, POSEIDON_WIDTH>
            + ExternalLayer<F, POSEIDON_WIDTH, POSEIDON_SBOX_DEGREE>,
        Poseidon2InternalLayerConstructor: InternalLayerConstructor<F> + InternalLayer<F, POSEIDON_WIDTH, POSEIDON_SBOX_DEGREE>,
        const POSEIDON_WIDTH: usize,
        const POSEIDON_SBOX_DEGREE: u64,
        const POSEIDON_SBOX_REGISTERS: usize,
        const POSEIDON_HALF_FULL_ROUNDS: usize,
        const POSEIDON_PARTIAL_ROUNDS: usize,
        const POSEIDON_VECTOR_LEN: usize,
    >
    PoseidonMerkleTreeAir<
        F,
        LinearLayers,
        Poseidon2ExternalLayerConstructor,
        Poseidon2InternalLayerConstructor,
        POSEIDON_WIDTH,
        POSEIDON_SBOX_DEGREE,
        POSEIDON_SBOX_REGISTERS,
        POSEIDON_HALF_FULL_ROUNDS,
        POSEIDON_PARTIAL_ROUNDS,
        POSEIDON_VECTOR_LEN,
    >
{
    pub fn new(leaves: Vec<[F; SECURE_WIDTH]>, leaf_index: usize) -> Self
    where
        StandardUniform: Distribution<F> + Distribution<[F; POSEIDON_WIDTH]>,
    {
        let mut rng = SmallRng::seed_from_u64(0);

        let poseidon_beginning_full_round_constants: [[F; POSEIDON_WIDTH];
            POSEIDON_HALF_FULL_ROUNDS] = core::array::from_fn(|_| rng.sample(StandardUniform));
        let poseidon_partial_round_constants: [F; POSEIDON_PARTIAL_ROUNDS] =
            core::array::from_fn(|_| rng.sample(StandardUniform));
        let poseidon_ending_full_round_constants: [[F; POSEIDON_WIDTH]; POSEIDON_HALF_FULL_ROUNDS] =
            core::array::from_fn(|_| rng.sample(StandardUniform));

        let poseidon_air_constant = RoundConstants::new(
            poseidon_beginning_full_round_constants,
            poseidon_partial_round_constants,
            poseidon_ending_full_round_constants,
        );

        let poseidon2_hasher = Self::new_poseidon_from_air_constants(
            poseidon_beginning_full_round_constants.clone(),
            poseidon_partial_round_constants.clone(),
            poseidon_ending_full_round_constants.clone(),
        );

        Self {
            poseidon_beginning_full_round_constants: poseidon_beginning_full_round_constants,
            poseidon_partial_round_constants: poseidon_partial_round_constants,
            poseidon_ending_full_round_constants: poseidon_ending_full_round_constants,

            poseidon2_air: Poseidon2Air::new(poseidon_air_constant.clone()),

            poseidon_constants: poseidon_air_constant,

            tree: Self::generate_merkle_tree(poseidon2_hasher.clone(), leaves),
            poseidon2_hasher: poseidon2_hasher,
            leaf_index: leaf_index,
            proof: vec![], //TODO: compute the correct proof.
        }
    }

    /// Generate a Merkle tree from the leaves
    /// because we are using this in the intialization
    /// we can't use self.
    fn generate_merkle_tree(
        poseidon2_hasher: Poseidon2<
            F,
            Poseidon2ExternalLayerConstructor,
            Poseidon2InternalLayerConstructor,
            POSEIDON_WIDTH,
            POSEIDON_SBOX_DEGREE,
        >,
        leaves: Vec<[F; SECURE_WIDTH]>,
    ) -> Vec<[F; SECURE_WIDTH]> {
        let mut tree = Vec::new();

        // Hash each leaf and add to the tree
        let mut current_level = leaves
            .iter()
            .map(|leaf| Self::hash_leaf(poseidon2_hasher.clone(), *leaf))
            .collect::<Vec<_>>();

        tree.extend_from_slice(&current_level);

        // Build the tree upwards
        while current_level.len() > 1 {
            // println!("tree at level {:?} is {:?}", current_level.len(), tree);
            let mut next_level = Vec::new();

            for chunk in current_level.chunks(2) {
                next_level.push(Self::hash_children(
                    poseidon2_hasher.clone(),
                    chunk[0],
                    chunk[1],
                ));
            }

            current_level = next_level;
            let mut new_tree = current_level.clone();
            new_tree.extend_from_slice(&tree);
            tree = new_tree;
        }

        // println!("tree at level {:?} is {:?}", current_level.len(), tree);

        tree
    }

    fn hash_leaf(
        poseidon2_hasher: Poseidon2<
            F,
            Poseidon2ExternalLayerConstructor,
            Poseidon2InternalLayerConstructor,
            POSEIDON_WIDTH,
            POSEIDON_SBOX_DEGREE,
        >,
        leaf: [F; SECURE_WIDTH],
    ) -> [F; SECURE_WIDTH] {
        Self::hash_children(poseidon2_hasher, leaf, [F::ZERO; SECURE_WIDTH])
    }

    fn hash_children(
        poseidon2_hasher: Poseidon2<
            F,
            Poseidon2ExternalLayerConstructor,
            Poseidon2InternalLayerConstructor,
            POSEIDON_WIDTH,
            POSEIDON_SBOX_DEGREE,
        >,
        left_child: [F; SECURE_WIDTH],
        right_child: [F; SECURE_WIDTH],
    ) -> [F; SECURE_WIDTH] {
        let mut input = [F::ZERO; POSEIDON_WIDTH];
        input.copy_from_slice(
            [left_child.as_slice(), right_child.as_slice()]
                .concat()
                .as_slice(),
        );
        let mut parent: [F; SECURE_WIDTH] = [F::ZERO; SECURE_WIDTH];
        parent.copy_from_slice(&poseidon2_hasher.permute(input)[0..SECURE_WIDTH]);
        // println!("input: {:?}, parent: {:?}", input, parent);
        parent
    }

    // pub fn generate_vectorized_trace_rows(
    //     &self,
    //     num_hashes: usize,
    //     extra_capacity_bits: usize,
    // ) -> RowMajorMatrix<F>
    // where
    //     F: PrimeField,
    //     LinearLayers: GenericPoseidon2LinearLayers<F, POSEIDON_WIDTH>,
    //     Standard: Distribution<[F; POSEIDON_WIDTH]>,
    // {
    //     let inputs = (0..num_hashes).map(|_| random()).collect::<Vec<_>>();
    //     generate_vectorized_trace_rows::<
    //         F,
    //         LinearLayers,
    //         POSEIDON_WIDTH,
    //         POSEIDON_SBOX_DEGREE,
    //         POSEIDON_SBOX_REGISTERS,
    //         POSEIDON_HALF_FULL_ROUNDS,
    //         POSEIDON_PARTIAL_ROUNDS,
    //         POSEIDON_VECTOR_LEN,
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

    fn number_of_non_leaf_nodes() -> usize {
        (1 << (TREE_HEIGHT - 1)) - 1
    }

    // Root node at index 0.
    // Left child of node at index i is at 2*i + 1.
    // Right child of node at index i is at 2*i + 2.
    // Parent of node at index i is at (i - 1) / 2

    /// return leaf index in the tree vec Leaf tree index = number of internal nodes + leaf-index - 1
    fn leaf_index_to_tree_index(leaf_index: usize) -> usize {
        Self::number_of_non_leaf_nodes() + leaf_index
    }

    /// return the index of the sibling of a node
    fn sibling_index(index: usize) -> usize {
        index - 2 * Self::is_right_sibling(index) + 1
    }

    /// return true if it is a 1 sibling otherwise 0
    #[inline]
    fn is_right_sibling(index: usize) -> usize {
        1 - index % 2
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

    fn generate_merkle_proof_trace(&self) -> RowMajorMatrix<F>
    where
        LinearLayers: GenericPoseidon2LinearLayers<F, POSEIDON_WIDTH>,
    {
        //We put all rows with all their columns in a flat vector and then we'll
        //tell plonky to turn it into a nice a table with number of columns
        //There are two columns in our air table and the number of steps is the
        //depth of the tree.
        let mut values = Vec::with_capacity(TREE_HEIGHT * POSEIDON_VECTOR_LEN);

        //we can just fill up the columns from the tree
        let mut current_node = Self::leaf_index_to_tree_index(self.leaf_index);

        //not clear what are these for
        let extra_capacity_bits = 0;
        let mut poseidon_matrix_width = 0;

        for _ in 0..TREE_HEIGHT {
            //We need to know if we are the right node or
            //the left node to hash in correct order.
            let sibling_node = match current_node {
                0 => [<F as PrimeCharacteristicRing>::ZERO; SECURE_WIDTH],
                _ => self.tree[Self::sibling_index(current_node)],
            };

            let (rightessness, siblings_concatinated) = match Self::is_right_sibling(current_node) {
                0 => (
                    <F as PrimeCharacteristicRing>::ZERO,
                    [self.tree[current_node], sibling_node].concat(),
                ),
                _ => (
                    <F as PrimeCharacteristicRing>::ONE,
                    [sibling_node, self.tree[current_node]].concat(),
                ),
            };

            values.push(rightessness);
            //we do not need to push the input, the input is
            //included in posseiden trace.
            // for i in 0..SECURE_WIDTH * 2 {
            //     values.push(siblings_concatinated[i]);
            // }

            //if we are at the root then there is no sibling
            //we pad the sibling with 0 just to make poseiden check to pass
            // println!("matrix update 01 :");
            pretty_print_matrix_vector(values.clone());

            let mut concat_input: [F; POSEIDON_WIDTH] = [F::ZERO; POSEIDON_WIDTH];
            concat_input.copy_from_slice(&siblings_concatinated);
            // println!("concat_input: {:?}", concat_input);
            let inputs = vec![concat_input; POSEIDON_VECTOR_LEN];
            // println!("inputs: {:?}",inputs);
            //let permutable_input = inputs.clone()[0];
            let poseidon_matrix =
                generate_vectorized_trace_rows::<
                    F,
                    LinearLayers,
                    POSEIDON_WIDTH,
                    POSEIDON_SBOX_DEGREE,
                    POSEIDON_SBOX_REGISTERS,
                    POSEIDON_HALF_FULL_ROUNDS,
                    POSEIDON_PARTIAL_ROUNDS,
                    POSEIDON_VECTOR_LEN,
                >(inputs, &self.poseidon_constants, extra_capacity_bits);

            //let permuted_output = self.poseidon2_hasher.permute(permutable_input);

            // println!("poseiden input {:?} \n and output {:?} ", permutable_input, permuted_output);
            // println!("poseiden row has {} width and {} height", poseidon_matrix.width(), poseidon_matrix.height());
            for j in 0..poseidon_matrix.width() {
                // .step_by(SECURE_WIDTH) {
                values.push(poseidon_matrix.get(0, j));
            }
            poseidon_matrix_width = poseidon_matrix.width();
            // println!("matrix update:");
            // pretty_print_matrix_vector(values.clone());

            if current_node != 0 {
                current_node = Self::parent_index(current_node);
            }
        }

        // println!("final values has length {}\n", values.len());
        //pretty_print_matrix_vector(values.clone());

        RowMajorMatrix::new(values, 1 + poseidon_matrix_width)
    }

    fn new_poseidon_from_air_constants(
        poseidon_beginning_full_round_constants: [[F; POSEIDON_WIDTH]; POSEIDON_HALF_FULL_ROUNDS],
        poseidon_partial_round_constants: [F; POSEIDON_PARTIAL_ROUNDS],
        poseidon_ending_full_round_constants: [[F; POSEIDON_WIDTH]; POSEIDON_HALF_FULL_ROUNDS],
    ) -> Poseidon2<
        F,
        Poseidon2ExternalLayerConstructor,
        Poseidon2InternalLayerConstructor,
        POSEIDON_WIDTH,
        POSEIDON_SBOX_DEGREE,
    > {
        let external_constants = ExternalLayerConstants::new(
            poseidon_beginning_full_round_constants.to_vec(),
            poseidon_ending_full_round_constants.to_vec(),
        );

        return Poseidon2::<
            F,
            Poseidon2ExternalLayerConstructor,
            Poseidon2InternalLayerConstructor,
            POSEIDON_WIDTH,
            POSEIDON_SBOX_DEGREE,
        >::new(
            external_constants,
            poseidon_partial_round_constants.to_vec(),
        );
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
        F: Field + InjectiveMonomial<POSEIDON_SBOX_DEGREE>,
        LinearLayers: Sync,
        Poseidon2ExternalLayerConstructor: ExternalLayerConstructor<F, POSEIDON_WIDTH>
            + ExternalLayer<F, POSEIDON_WIDTH, POSEIDON_SBOX_DEGREE>
            + Sync,
        Poseidon2InternalLayerConstructor: InternalLayerConstructor<F> + InternalLayer<F, POSEIDON_WIDTH, POSEIDON_SBOX_DEGREE> + Sync,
        const POSEIDON_WIDTH: usize,
        const POSEIDON_SBOX_DEGREE: u64,
        const POSEIDON_SBOX_REGISTERS: usize,
        const POSEIDON_HALF_FULL_ROUNDS: usize,
        const POSEIDON_PARTIAL_ROUNDS: usize,
        const POSEIDON_VECTOR_LEN: usize,
    > BaseAir<F>
    for PoseidonMerkleTreeAir<
        F,
        LinearLayers,
        Poseidon2ExternalLayerConstructor,
        Poseidon2InternalLayerConstructor,
        POSEIDON_WIDTH,
        POSEIDON_SBOX_DEGREE,
        POSEIDON_SBOX_REGISTERS,
        POSEIDON_HALF_FULL_ROUNDS,
        POSEIDON_PARTIAL_ROUNDS,
        POSEIDON_VECTOR_LEN,
    >
{
    fn width(&self) -> usize {
        // println!("width is {}", 16 + self.poseidon2_air.width() * POSEIDON_VECTOR_LEN);
        1 + self.poseidon2_air.width() * POSEIDON_VECTOR_LEN
        // It will be hash of a node and its sibling plus as many column we need for Poseidon
    }
}

impl<
        AB: AirBuilder,
        LinearLayers: GenericPoseidon2LinearLayers<AB::Expr, POSEIDON_WIDTH>,
        Poseidon2ExternalLayerConstructor: ExternalLayerConstructor<AB::F, POSEIDON_WIDTH>
            + ExternalLayer<AB::F, POSEIDON_WIDTH, POSEIDON_SBOX_DEGREE>
            + Sync,
        Poseidon2InternalLayerConstructor: InternalLayerConstructor<AB::F>
            + InternalLayer<AB::F, POSEIDON_WIDTH, POSEIDON_SBOX_DEGREE>
            + Sync,
        const POSEIDON_WIDTH: usize,
        const POSEIDON_SBOX_DEGREE: u64,
        const POSEIDON_SBOX_REGISTERS: usize,
        const POSEIDON_HALF_FULL_ROUNDS: usize,
        const POSEIDON_PARTIAL_ROUNDS: usize,
        const POSEIDON_VECTOR_LEN: usize,
    > Air<AB>
    for PoseidonMerkleTreeAir<
        AB::F,
        LinearLayers,
        Poseidon2ExternalLayerConstructor,
        Poseidon2InternalLayerConstructor,
        POSEIDON_WIDTH,
        POSEIDON_SBOX_DEGREE,
        POSEIDON_SBOX_REGISTERS,
        POSEIDON_HALF_FULL_ROUNDS,
        POSEIDON_PARTIAL_ROUNDS,
        POSEIDON_VECTOR_LEN,
    >
where
    AB::F: PrimeField + InjectiveMonomial<POSEIDON_SBOX_DEGREE>,
    AB::Var: Debug,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0); //we are climbing up the tree
        let next = main.row_slice(1);
        // Enforce starting values: make sure they are equal to the leaves
        // First we should know if we are right or left leave. even = left, odd = right
        // let neighbour_index = match(leaf_index % 2) {
        //     0 => leaf_index + 1,
        //     1 => leaf_index - 1,
        // };

        //let poseidon2 = Poseidon2Merkle::<AB::F>;

        //local (length SECURE_WIDTH * 2 + POSEIDEN_WIDTH * (half_full_rounds*2+partial rounds))
        //                (8 * 2 + 16 * (4*2 + 20)) * 2  (* (+ (* 2 8) (* 16 (+ (* 2 4) 20)  ) ) 1) 464 then why 329
        // (- 329 313) so 313 from poseiden which you think should be divisable by 16
        // (- 464 16) (/ 448 28)
        // (/ 313 16.0) is almost 20 how does it work?
        //
        // println!("length of local is {}", local.len());
        let LEFT_INPUT_INDEX = 2; //selector col plus length col
        let RIGHT_INPUT_INDEX = 2 + SECURE_WIDTH; //selector col plus length col plus left input

        //First row is dealing with hash of leaves
        for i in 0..SECURE_WIDTH {
            //println!("local[0]: {:?}, local[{i}+1]:{:?}, local[{i}+1+{SECURE_WIDTH}]:{:?}, self.tree[Self::leaf_index_to_tree_index(self.leaf_index)][0]:{:?}", local[0], local[1+i],local[i+1+SECURE_WIDTH], self.tree[Self::leaf_index_to_tree_index(self.leaf_index)][i]);

            builder.when_first_row().assert_eq(
                local[0] * local[i + RIGHT_INPUT_INDEX]
                    + (AB::Expr::from(AB::F::ONE) - local[0]) * local[i + LEFT_INPUT_INDEX],
                <AB::Expr as From<AB::F>>::from(
                    self.tree[Self::leaf_index_to_tree_index(self.leaf_index)][i],
                ),
            );
        }
        // println!("We pass frist assert");

        //Assuming the leafs are already hash of something
        // println!("the index of the leaf's in the tree :{}", Self::leaf_index_to_tree_index(self.leaf_index));
        // println!("the index of the leaf's sibling in the tree :{}", Self::sibling_index(Self::leaf_index_to_tree_index(self.leaf_index)));
        // println!("local[1]:{:?}  should be hash of leaf's sibling and first element of the proof:{}",  local[SECURE_WIDTH], self.tree[Self::sibling_index(Self::leaf_index_to_tree_index(self.leaf_index))][0]);

        // builder.when_first_row().assert_eq(
        //     local[0 + SECURE_WIDTH], //poseidon2.permute(
        //     //            [
        //     self.tree[Self::sibling_index(Self::leaf_index_to_tree_index(self.leaf_index))][0],
        //     //         ZERO_PAD
        //     //     ]
        //     // )[0..SECURE_WIDTH]
        // ); //Probably redundant (column 1 is input)

        // println!("We pass second assert");

        //In the last row we should not verify Posieden
        let poseidon_part = local[1..].to_vec();
        // println!("poseidon_part has length {}", poseidon_part.len());
        // println!("poseidon_part is {:?}", poseidon_part);
        //we verify that poseidon2 is evaluated correctly
        let poseidon_local: &VectorizedPoseidon2Cols<
            _,
            POSEIDON_WIDTH,
            POSEIDON_SBOX_DEGREE,
            POSEIDON_SBOX_REGISTERS,
            POSEIDON_HALF_FULL_ROUNDS,
            POSEIDON_PARTIAL_ROUNDS,
            POSEIDON_VECTOR_LEN,
        > = (*poseidon_part).borrow();

        let i = 0;
        for perm in &poseidon_local.cols {
            // println!("verifying poseidon perm number {i}");
            air_eval(&self.poseidon2_air, builder, perm);
        }

        // Enforce state transition constraintse
        // next is parent, it should be equal hash of childs
        for i in 0..SECURE_WIDTH {
            // println!("comparing local {} element: {:?} and next {} element: {:?}", local.len() - (SECURE_WIDTH * 2) + i, local[local.len() - (SECURE_WIDTH * 2) + i], i, next[i + 1]);
            // println!("or comparing local {} element: {:?} and next {} element: {:?}", local.len() - (SECURE_WIDTH * 2) + i, local[local.len() - (SECURE_WIDTH * 2) + i], i + SECURE_WIDTH, next[1 + i + SECURE_WIDTH]);
            // println!("right: {:?} left: {:?}",next[0] * next[i + 1 + SECURE_WIDTH]  + (AB::Expr::from(AB::F::ONE) - next[0])*next[1 + i], local[local.len() - (SECURE_WIDTH * 2) + i]);
            builder.when_transition().assert_eq(
                next[0] * next[i + RIGHT_INPUT_INDEX]
                    + (AB::Expr::from(AB::F::ONE) - next[0]) * next[LEFT_INPUT_INDEX + i],
                local[local.len() - (SECURE_WIDTH * 2) + i],
            );
        }
        //builder.when_tansition().assert_eq(next[1], local[0] + local[1]);

        // Constrain the final value
        let merkle_root = self.tree[0];

        for i in 0..SECURE_WIDTH {
            // println!("local[0]: {:?}, local[{i}+1]:{:?}, local[{i}+1+{SECURE_WIDTH}]:{:?}, self.tree[Self::leaf_index_to_tree_index(self.leaf_index)][0]:{:?}", local[0], local[1+i],local[i+1+SECURE_WIDTH], self.tree[Self::leaf_index_to_tree_index(self.leaf_index)][i]);

            builder.when_last_row().assert_eq(
                local[0] * local[i + RIGHT_INPUT_INDEX]
                    + (AB::Expr::from(AB::F::ONE) - local[0]) * local[LEFT_INPUT_INDEX + i],
                <AB::Expr as From<AB::F>>::from(merkle_root[i]),
            );
        }
    }
}

const POSEIDON_WIDTH: usize = 16;
const POSEIDON_SBOX_DEGREE: u64 = 5;
const POSEIDON_SBOX_REGISTERS: usize = 1;
const POSEIDON_HALF_FULL_ROUNDS: usize = 4;
const POSEIDON_PARTIAL_ROUNDS: usize = 20;
const POSEIDON_VECTOR_LEN: usize = 1; //1 << 3;

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

    let leave_layer_size = 1 << TREE_HEIGHT - 1;

    let leaves = generate_random_leaves(leave_layer_size, 0);

    let leaf_index: usize = 1;

    let air = PoseidonMerkleTreeAir::<
        Val,
        GenericPoseidon2LinearLayersMersenne31,
        Poseidon2ExternalLayerMersenne31<POSEIDON_WIDTH>,
        Poseidon2InternalLayerMersenne31,
        POSEIDON_WIDTH,
        POSEIDON_SBOX_DEGREE,
        POSEIDON_SBOX_REGISTERS,
        POSEIDON_HALF_FULL_ROUNDS,
        POSEIDON_PARTIAL_ROUNDS,
        POSEIDON_VECTOR_LEN,
    >::new(leaves, leaf_index);
    let trace = air.generate_merkle_proof_trace();

    let challenger = Challenger::from_hasher(vec![], byte_hash);

    type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;
    let config = MyConfig::new(pcs, challenger);

    let proof = prove(&config, &air, trace, &vec![]);

    let bin_config = bincode::config::standard()
        .with_little_endian()
        .with_fixed_int_encoding();
    let proof_bytes = bincode::serde::encode_to_vec(proof.borrow(), bin_config)
        .expect("Failed to serialize proof");
    println!("Proof size: {} bytes", proof_bytes.len());

    verify(&config, &air, &proof, &vec![])
}

fn generate_random_leaves<F: PrimeField>(
    leave_layer_size: usize,
    randomness_seed: u64,
) -> Vec<[F; SECURE_WIDTH]>
where
    StandardUniform: Distribution<[F; SECURE_WIDTH]>,
{
    let mut rng = SmallRng::seed_from_u64(randomness_seed);

    (0..leave_layer_size)
        .map(|_| rng.random())
        .collect::<Vec<_>>()
}

fn pretty_print_matrix_vector<F: Field>(values: Vec<F>) {
    // print!("[ ");
    // for i in 0..values.len(){
    //     print!("{}, ", values[i]);
    // }
    // println!(" ]");
}

#[cfg(test)]
mod test {
    fn test_check_index_to_tree_works() {}
}
