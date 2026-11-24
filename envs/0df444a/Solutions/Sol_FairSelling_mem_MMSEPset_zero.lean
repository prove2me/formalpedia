-- Prove2me | solution 1 for FairSelling.mem_MMSEPset_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:22:48.964628+00:00
-- url     : https://prove2.me/submissions/c335b16d-2b2f-4fbc-8588-528583000bb6

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds

set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (v p : G → ℝ) : (0 : ℝ) ∈ MMSEPset n v p := by
  refine ⟨⟨∅, fun _ => ∅, fun _ => 0⟩, ?_, ?_, ?_⟩ <;>
    simp [Outcome.Valid, Outcome.EqualProceeds, util]
end FairSelling
