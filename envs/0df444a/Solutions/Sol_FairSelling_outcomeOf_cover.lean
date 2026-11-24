-- Prove2me | solution 1 for FairSelling.outcomeOf_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:28:08.522251+00:00
-- url     : https://prove2.me/submissions/2559b54c-7798-4082-bbf4-379f087a3370

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
namespace FairSelling
theorem _root_.solution (assign : G → Option (Fin n)) (m : Fin n → ℝ) :
    (outcomeOf assign m).sold ∪ Finset.univ.biUnion (outcomeOf assign m).kept = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro g
  simp only [outcomeOf, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion]
  rcases h : assign g with _ | i
  · exact Or.inl rfl
  · exact Or.inr ⟨i, rfl⟩
end FairSelling
