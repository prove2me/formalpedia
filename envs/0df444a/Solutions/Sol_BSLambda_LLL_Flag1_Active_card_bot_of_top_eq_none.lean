-- Prove2me | solution 1 for BSLambda.LLL.Flag1.Active.card_bot_of_top_eq_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:03:37.72769+00:00
-- url     : https://prove2.me/submissions/938273c5-4bb2-4a78-a2ae-7ae5df7fa0bb

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_Flag1_active_iff_of_top_eq_none

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
theorem _root_.solution (ha : F.top = none) : F.bot.card = 4 :=
  ((active_iff_of_top_eq_none ha).1 hF).2.1
end BSLambda.LLL.Flag1.Active
