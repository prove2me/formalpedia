-- Prove2me | solution 1 for BSLambda.lam_le_of_sensAt_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:35:45.879496+00:00
-- url     : https://prove2.me/submissions/decdb257-79b6-4cb0-bb65-687b73acdb98

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Bipartite
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Theorems.Thm_BSLambda_adj_nonneg
public import Theorems.Thm_BSLambda_lam_le_l2_opNorm_adj
public import Theorems.Thm_BSLambda_sum_adj_col
public import Theorems.Thm_BSLambda_sum_adj_row
public import Theorems.Thm_Matrix_l2_opNorm_le_sqrt_of_row_col_sums
attribute [local simp] BSLambda.sum_adj_row



set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix Matrix.Norms.L2Operator
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution {f : Input V → Bool} {k : ℝ} (hk : 0 ≤ k)
    (hs : ∀ x, (sensAt f x : ℝ) ≤ k) : lam f ≤ k := by
  refine (lam_le_l2_opNorm_adj f).trans ?_
  rw [← Real.sqrt_mul_self hk]
  exact Matrix.l2_opNorm_le_sqrt_of_row_col_sums (adj f) (adj_nonneg f)
    (fun x ↦ (sum_adj_row f x).trans_le (hs x)) fun y ↦ (sum_adj_col f y).trans_le (hs y)
end BSLambda
