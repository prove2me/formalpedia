-- Prove2me | solution 1 for FairSelling.outcomeOf_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:27:58.059286+00:00
-- url     : https://prove2.me/submissions/3b25e554-0a34-44ba-b23d-e7fabb6c722c

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [DecidableEq G]
namespace FairSelling
theorem _root_.solution (p : G → ℝ) (assign : G → Option (Fin n)) (m : Fin n → ℝ)
    (hm0 : ∀ j, 0 ≤ m j) (hms : ∑ j, m j ≤ procOf p assign) :
    (outcomeOf assign m).Valid p := by
  refine ⟨?_, ?_, hm0, ?_⟩
  · intro j
    refine Finset.disjoint_left.mpr ?_
    intro x hx1 hx2
    simp only [outcomeOf, Finset.mem_filter] at hx1 hx2
    rw [hx1.2] at hx2; exact absurd hx2.2 (by simp)
  · intro j k hjk
    refine Finset.disjoint_left.mpr ?_
    intro x hx1 hx2
    simp only [outcomeOf, Finset.mem_filter] at hx1 hx2
    rw [hx1.2] at hx2
    exact hjk (Option.some.inj hx2.2)
  · exact hms
end FairSelling
