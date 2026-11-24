-- Prove2me | solution 1 for FairSelling.fin3_others
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:23:54.028499+00:00
-- url     : https://prove2.me/submissions/948fa01c-3e7f-43d2-ad14-9d0f88d281a6

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
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (k : Fin 3) : ∃ j j' : Fin 3, j ≠ k ∧ j' ≠ k ∧ j ≠ j' := by
  fin_cases k
  · exact ⟨1, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide⟩
end FairSelling
