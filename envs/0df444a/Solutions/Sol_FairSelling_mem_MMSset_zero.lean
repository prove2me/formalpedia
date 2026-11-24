-- Prove2me | solution 1 for FairSelling.mem_MMSset_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:50:39.013843+00:00
-- url     : https://prove2.me/submissions/26be7c09-d51d-491b-9aa5-7e7ec82c8432

import Mathlib
import Definitions.Def_RequestProject_Selling

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) :
    (0 : ℝ) ∈ MMSset n v p := by
  -- The value for every agent is zero.
  use ⟨∅, fun _ => ∅, fun _ => 0⟩
  simp [Outcome.Valid, util]
end FairSelling
