-- Prove2me | solution 1 for FairSelling.outcome_of_bundles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T01:43:38.784805+00:00
-- url     : https://prove2.me/submissions/e3e40b77-a57d-4682-ba81-5aef6dcceaf8

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_ThreeAgentCashComposition
import Definitions.Def_RequestProject_MatchingPhase
import Theorems.Thm_FairSelling_unifiedOutcome_valid
import Theorems.Thm_FairSelling_util_unifiedOutcome


set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]
namespace FairSelling
theorem _root_.solution (v : Fin 3 → G → ℝ) (p : G → ℝ) (hp : ∀ g, 0 ≤ p g)
    (X : Fin 3 → Finset G) (F : Finset G) (q : Fin 3 → ℝ)
    (hX : ∀ i j, i ≠ j → Disjoint (X i) (X j)) (hF : ∀ i, Disjoint F (X i))
    (hq0 : ∀ i, 0 ≤ q i) (hq : ∑ i, q i ≤ ∑ g ∈ F, p g)
    (hval : ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ vbarSum (v i) p (X i) + q i) :
    ∃ o : Outcome G 3, o.Valid p ∧
      ∀ i, (3 / 4 : ℝ) * MMS 3 (v i) p ≤ util (v i) o i := by
  refine ⟨unifiedOutcome v p X F q, unifiedOutcome_valid v p hp X F q hX hF hq0 hq, fun i => ?_⟩
  rw [util_unifiedOutcome]
  exact hval i
end FairSelling
