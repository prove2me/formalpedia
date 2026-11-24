-- Prove2me | solution 1 for BSLambda.l2_opNorm_adj_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:22:52.094486+00:00
-- url     : https://prove2.me/submissions/4f59fb40-d30d-475a-b5f1-d789fe8c55d0

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_SchurTest
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Theorems.Thm_BSLambda_sum_ones_add_sum_zeros
public import Theorems.Thm_BSLambda_mulVec_adj_ones
public import Theorems.Thm_BSLambda_mulVec_adj_zeros
public import Theorems.Thm_BSLambda_card_nbrs
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_sum_adj_row
public import Theorems.Thm_BSLambda_zeroInput_apply
public import Theorems.Thm_Matrix_l2_opNorm_le_of_sum_sq_mulVec_le
public import Theorems.Thm_Matrix_l2_opNorm_transpose
public import Theorems.Thm_Matrix_sum_sq_mulVec_le
attribute [local simp] BSLambda.card_nbrs
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply
attribute [local simp] BSLambda.hammingDist_flipSet
attribute [local simp] BSLambda.sum_adj_row
attribute [local simp] BSLambda.zeroInput_apply



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) : ‖adj f‖ ≤ ‖biadj f‖ := by
  refine Matrix.l2_opNorm_le_of_sum_sq_mulVec_le (adj f) (norm_nonneg _) fun v ↦ ?_
  rw [← sum_ones_add_sum_zeros f fun y ↦ (adj f *ᵥ v) y ^ 2,
    ← sum_ones_add_sum_zeros f fun y ↦ v y ^ 2]
  have h1 : ∑ x : Ones f, (adj f *ᵥ v) x.1 ^ 2 ≤ ‖biadj f‖ ^ 2 * ∑ z : Zeros f, v z.1 ^ 2 := by
    simpa [mulVec_adj_ones] using Matrix.sum_sq_mulVec_le (biadj f) fun z : Zeros f ↦ v z.1
  have h2 : ∑ z : Zeros f, (adj f *ᵥ v) z.1 ^ 2 ≤ ‖biadj f‖ ^ 2 * ∑ x : Ones f, v x.1 ^ 2 := by
    simpa [mulVec_adj_zeros, Matrix.l2_opNorm_transpose] using
      Matrix.sum_sq_mulVec_le ((biadj f)ᵀ) fun x : Ones f ↦ v x.1
  calc ∑ x : Ones f, (adj f *ᵥ v) x.1 ^ 2 + ∑ z : Zeros f, (adj f *ᵥ v) z.1 ^ 2
      ≤ ‖biadj f‖ ^ 2 * ∑ z : Zeros f, v z.1 ^ 2 + ‖biadj f‖ ^ 2 * ∑ x : Ones f, v x.1 ^ 2 :=
        add_le_add h1 h2
    _ = ‖biadj f‖ ^ 2 * (∑ x : Ones f, v x.1 ^ 2 + ∑ z : Zeros f, v z.1 ^ 2) := by ring
end BSLambda
