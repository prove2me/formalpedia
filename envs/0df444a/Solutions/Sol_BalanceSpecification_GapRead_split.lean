-- Prove2me | solution 1 for BalanceSpecification.GapRead.split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:04:26.286128+00:00
-- url     : https://prove2.me/submissions/d76a89f5-ae7c-4d01-8568-9a2c26becc8f

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
theorem _root_.solution (h : GapRead S a (u ++ v) c) :
    ∃ b, GapRead S a u b ∧ GapRead S b v c := by
  induction u generalizing a with
  | nil => exact ⟨a, .nil a, h⟩
  | cons q u ih =>
    cases h with
    | zero h =>
      obtain ⟨b, hu, hv⟩ := ih h
      exact ⟨b, .zero hu, hv⟩
    | one hs h =>
      obtain ⟨b, hu, hv⟩ := ih h
      exact ⟨b, .one hs hu, hv⟩
end BalanceSpecification.GapRead
