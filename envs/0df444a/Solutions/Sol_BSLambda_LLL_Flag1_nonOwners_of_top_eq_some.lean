-- Prove2me | solution 1 for BSLambda.LLL.Flag1.nonOwners_of_top_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:01:09.857382+00:00
-- url     : https://prove2.me/submissions/ef4fb591-1c05-4482-b162-25b2b58f0fb4

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
theorem _root_.solution (ha : F.top = some a) : F.nonOwners = insert a F.bot := by
  rw [nonOwners, ha]
end BSLambda.LLL.Flag1
