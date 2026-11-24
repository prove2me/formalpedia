-- Prove2me | solution 1 for BSLambda.lam_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:44:06.854043+00:00
-- url     : https://prove2.me/submissions/d99052d4-c5b7-4eb1-82dc-3e33ebbe4196

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_OpNorm
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Composition
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Spectral_Multiplicative
public import Theorems.Thm_BSLambda_sum_sq_adj_comp_mulVec_le
public import Theorems.Thm_BSLambda_lam_le_l2_opNorm_adj
public import Theorems.Thm_BSLambda_lam_nonneg
public import Theorems.Thm_Matrix_l2_opNorm_le_of_sum_sq_mulVec_le


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open scoped Matrix
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
namespace BSLambda
theorem _root_.solution (f : Input W → Bool) (g : Input V → Bool) :
    lam (comp f g) ≤ lam f * lam g :=
  (lam_le_l2_opNorm_adj (comp f g)).trans
    (Matrix.l2_opNorm_le_of_sum_sq_mulVec_le (adj (comp f g))
      (mul_nonneg (lam_nonneg f) (lam_nonneg g)) (sum_sq_adj_comp_mulVec_le f g))
end BSLambda
