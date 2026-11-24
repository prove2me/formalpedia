-- Prove2me | solution 1 for BSLambda.LLL.Flag1.nonOwners_of_top_eq_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:01:15.663518+00:00
-- url     : https://prove2.me/submissions/e6c6e0d9-fb67-476e-810f-645ed73e6699

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction

set_option autoImplicit true
@[expose] public section
public section
open BSLambda
open BSLambda.LLL
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}
open BSLambda.LLL.Flag1
omit [Fintype ι]
variable {F : Flag1 ι} {Arc : ι → ι → Bool} {a j : ι} {p : ι × ι}
namespace BSLambda.LLL.Flag1
theorem _root_.solution (ha : F.top = none) : F.nonOwners = F.bot := by
  rw [nonOwners, ha]
end BSLambda.LLL.Flag1
