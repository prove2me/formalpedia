-- Prove2me | solution 1 for BalanceSpecification.GapRead.gapState_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:31:47.515187+00:00
-- url     : https://prove2.me/submissions/fdfbca71-967a-4d7f-8fb3-c83228b4b1b1

module
public import Definitions.Def_BalanceSpecificaton_CodedLanguage
public import Definitions.Def_BalanceSpecificaton_Periodicity
public import Definitions.Def_BalanceSpecificaton_SGapBounds
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_SGap

set_option autoImplicit true
@[expose] public section
public section
open BalanceSpecification
open BalanceSpecification.GapRead
variable {S : Set ℕ} {a b c : ℕ} {u v : Word Bool}
namespace BalanceSpecification.GapRead
theorem _root_.solution (h : GapRead S a u b) (ha : GapState S a) : GapState S b := by
  induction h with
  | nil => exact ha
  | zero _ ih =>
    obtain ⟨s, hs, hle⟩ := ha
    exact ih ⟨s, hs, by omega⟩
  | one hs _ ih => exact ih ⟨_, hs, le_rfl⟩
end BalanceSpecification.GapRead
