-- Prove2me | solution 1 for BalanceSpecification.predecessor_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:16:13.252675+00:00
-- url     : https://prove2.me/submissions/9d22ad3b-2607-4461-b5b1-f7abe97b4949

module
public import Definitions.Def_BalanceSpecificaton_Language
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic
public import Definitions.Def_BalanceSpecificaton_Counting

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open BalanceSpecification
variable {A : Type*} [Fintype A]
namespace BalanceSpecification
theorem _root_.solution (L : Set (Word A)) (u : Word A) (n : ℕ) :
    (predecessorFinset L u n).card ≤ wordCount L n := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)
end BalanceSpecification
