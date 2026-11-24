-- Prove2me | solution 1 for BSLambda.LLL.radiusTwoConst_eq_nine_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:28:14.710639+00:00
-- url     : https://prove2.me/submissions/947bb2ad-47fa-443f-a860-1a836beb58cb

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_Numerics_radiusTwoSum_eq
public import Theorems.Thm_BSLambda_PartialAssign_Conflict_symm


set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
namespace BSLambda.LLL
theorem _root_.solution : radiusTwoConst = 9 * radiusTwoOwnerConst := by
  rw [radiusTwoConst, radiusTwoOwnerConst, ← mul_assoc]
  exact Numerics.radiusTwoSum_eq.symm
end BSLambda.LLL
