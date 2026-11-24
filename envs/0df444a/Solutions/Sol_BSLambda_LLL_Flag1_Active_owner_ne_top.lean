-- Prove2me | solution 1 for BSLambda.LLL.Flag1.Active.owner_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:03:00.017332+00:00
-- url     : https://prove2.me/submissions/52b50d5a-4f5d-4888-9e7a-71581ddaeefb

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_Flag1_active_iff_of_top_eq_some

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
open BSLambda.LLL.Flag1.Active
variable (hF : F.Active Arc)
include hF
namespace BSLambda.LLL.Flag1.Active
theorem _root_.solution (ha : F.top = some a) : F.owner ≠ a :=
  ((active_iff_of_top_eq_some ha).1 hF).1
end BSLambda.LLL.Flag1.Active
