-- Prove2me | solution 1 for FairSelling.MMSset_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T01:38:05.19502+00:00
-- url     : https://prove2.me/submissions/c0c5fece-f034-4482-81e4-b0dc2c9e61b2

import Mathlib
import Definitions.Def_RequestProject_Selling
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [Fintype G] [DecidableEq G]


theorem solution (v p : G → ℝ) :
    (MMSset n v p).Nonempty := by
  let o : Outcome G n := ⟨∅, fun _ => ∅, fun _ => 0⟩
  refine ⟨0,o,?_,?_⟩ <;> simp [o, Outcome.Valid, util]
