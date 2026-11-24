-- Prove2me | solution 1 for BalanceSpecification.follower_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:50:23.211281+00:00
-- url     : https://prove2.me/submissions/24c3c129-5670-453e-832d-5a1a4edfe34b

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
    (followerFinset L u n).card ≤ wordCount L n := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)
end BalanceSpecification
