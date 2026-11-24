-- Prove2me | solution 1 for FairSelling.matching_phase_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:58:25.814762+00:00
-- url     : https://prove2.me/submissions/98ea1879-e4ac-41ff-a4ac-749be7c0c624

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase

set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
namespace FairSelling
theorem _root_.solution (acc : Fin 2 → Fin 2 → Bool) :
    (∃ σ : Equiv.Perm (Fin 2), ∀ j, acc j (σ j) = true)
    ∨ (∃ k, ∀ j, acc j k = false)
    ∨ (∃ j j' : Fin 2, j ≠ j' ∧ (∀ k, acc j k = true) ∧ (∀ k, acc j' k = false)) := by
  revert acc
  decide
end FairSelling
