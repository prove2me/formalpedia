-- Prove2me | solution 1 for BSLambda.lam_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:22:30.393222+00:00
-- url     : https://prove2.me/submissions/47f5f784-5596-4a42-8da7-0ae7a839470d

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Sensitivity
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Hermitian
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Spectral
public import Theorems.Thm_BSLambda_card_nbrs
public import Theorems.Thm_BSLambda_sum_adj_row
public import Theorems.Thm_BSLambda_trace_adj
public import Theorems.Thm_BSLambda_flipSet_apply_eq_self_iff
public import Theorems.Thm_BSLambda_flipSet_apply_of_mem
public import Theorems.Thm_BSLambda_flipSet_apply_of_notMem
public import Theorems.Thm_BSLambda_flipSet_empty
public import Theorems.Thm_BSLambda_flipSet_flipSet
public import Theorems.Thm_BSLambda_flipSet_left_inj
public import Theorems.Thm_BSLambda_flipSet_zeroInput_apply
public import Theorems.Thm_BSLambda_hammingDist_flipSet
public import Theorems.Thm_BSLambda_zeroInput_apply
attribute [local simp] BSLambda.flipSet_apply_eq_self_iff
attribute [local simp] BSLambda.flipSet_apply_of_mem
attribute [local simp] BSLambda.flipSet_apply_of_notMem
attribute [local simp] BSLambda.flipSet_empty
attribute [local simp] BSLambda.flipSet_flipSet
attribute [local simp] BSLambda.flipSet_left_inj
attribute [local simp] BSLambda.flipSet_zeroInput_apply
attribute [local simp] BSLambda.hammingDist_flipSet
attribute [local simp] BSLambda.zeroInput_apply


attribute [local simp] BSLambda.card_nbrs
attribute [local simp] BSLambda.sum_adj_row

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V]
variable [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input V → Bool) : 0 ≤ lam f := by
  have htr : ∑ i, (isHermitian_adj f).eigenvalues i = 0 := by
    simpa [trace_adj] using (isHermitian_adj f).trace_eq_sum_eigenvalues.symm
  have hle : ∑ _i : Input V, (0 : ℝ) ≤ ∑ i, (isHermitian_adj f).eigenvalues i := by
    rw [htr, Finset.sum_const_zero]
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hle
  exact hi.trans (le_ciSup (Finite.bddAbove_range _) i)
end BSLambda
