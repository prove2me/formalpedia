-- Prove2me | solution 1 for BSLambda.LLL.Flag1.Active.card_nonOwners
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:27:00.164185+00:00
-- url     : https://prove2.me/submissions/acb7f718-f259-45fd-b83f-7cd55cd00083

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_Flag1_nonOwners_of_top_eq_none
public import Theorems.Thm_BSLambda_LLL_Flag1_nonOwners_of_top_eq_some
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_card_bot_of_top_eq_none
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_card_bot_of_top_eq_some
public import Theorems.Thm_BSLambda_LLL_Flag1_Active_top_notMem_bot

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
theorem _root_.solution : F.nonOwners.card = 4 := by
  cases ha : F.top with
  | none => rw [nonOwners_of_top_eq_none ha, hF.card_bot_of_top_eq_none ha]
  | some a =>
    rw [nonOwners_of_top_eq_some ha, Finset.card_insert_of_notMem (hF.top_notMem_bot ha),
      hF.card_bot_of_top_eq_some ha]
end BSLambda.LLL.Flag1.Active
