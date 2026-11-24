-- Prove2me | solution 1 for BSLambda.LLL.Flag1.active_iff_of_top_eq_some
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:01:56.553215+00:00
-- url     : https://prove2.me/submissions/f4a8e129-94e3-459f-9608-c4e58fe5893d

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Construction_Basic
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Numerics_Binomial
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Obstruction
public import Theorems.Thm_BSLambda_LLL_Flag1_nonOwners_of_top_eq_some

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
theorem _root_.solution (ha : F.top = some a) :
    F.Active Arc ↔ F.owner ≠ a ∧ F.owner ∉ F.bot ∧ a ∉ F.bot ∧ F.bot.card = 3 ∧
      Arc a F.owner = true ∧ ∀ j ∈ F.bot, Arc F.owner j = true ∧ Arc a j = true := by
  rw [Active, nonOwners_of_top_eq_some ha, ha, Finset.mem_insert, not_or, and_assoc]
end BSLambda.LLL.Flag1
