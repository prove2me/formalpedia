-- Prove2me | solution 1 for FairSelling.swapOutcome_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:29:08.336806+00:00
-- url     : https://prove2.me/submissions/f5327cf1-7292-4ddb-af63-766001f68c54

import Mathlib
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TwoAgents

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (p : G → ℝ) (o : Outcome G 2) (h : o.Valid p) :
    (swapOutcome o).Valid p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun i => h1 _, fun i j hij => h2 _ _ (fun he => hij ((Equiv.swap 0 1).injective he)),
    fun i => h3 _, ?_⟩
  show ∑ i, o.money (Equiv.swap 0 1 i) ≤ _
  rw [Equiv.sum_comp (Equiv.swap 0 1) o.money]; exact h4
end FairSelling
