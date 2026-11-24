-- Prove2me | solution 1 for BSLambda.LLL.Flag1.Active.arc_owner_bot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:03:34.780511+00:00
-- url     : https://prove2.me/submissions/fe2121d1-688d-4380-aaa1-c21caf0eae5b

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_Flag1_active_iff_of_top_eq_none
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
theorem _root_.solution (hj : j ∈ F.bot) : Arc F.owner j = true := by
  cases ha : F.top with
  | none => exact ((active_iff_of_top_eq_none ha).1 hF).2.2 j hj
  | some a => exact (((active_iff_of_top_eq_some ha).1 hF).2.2.2.2.2 j hj).1
end BSLambda.LLL.Flag1.Active
