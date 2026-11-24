-- Prove2me | solution 1 for BSLambda.LLL.Flag1.active_iff_of_top_eq_none
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:02:57.232692+00:00
-- url     : https://prove2.me/submissions/9e285938-7991-437a-969a-07732bb225a8

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_Flag1_nonOwners_of_top_eq_none

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
theorem _root_.solution (ha : F.top = none) :
    F.Active Arc ↔ F.owner ∉ F.bot ∧ F.bot.card = 4 ∧ ∀ j ∈ F.bot, Arc F.owner j = true := by
  rw [Active, nonOwners_of_top_eq_none ha, ha]
end BSLambda.LLL.Flag1
