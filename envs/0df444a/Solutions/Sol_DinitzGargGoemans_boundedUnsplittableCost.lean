-- Prove2me | solution 1 for DinitzGargGoemans.boundedUnsplittableCost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:02:41.040448+00:00
-- url     : https://prove2.me/submissions/37b05d65-0f79-474f-a710-c0e590773f00

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
import Theorems.Thm_DinitzGargGoemans_unsplittableCostEqPaidCount
import Theorems.Thm_DinitzGargGoemans_boundedRoutingHasTwoPaid

set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans
namespace DinitzGargGoemans
theorem _root_.solution (q : Commodity → RouteChoice)
    (bound : ∀ a,
      unsplittableLoad counterexampleInstance q a ≤
        fractionalLoad counterexampleInstance splitFlow a +
          maximumDemand counterexampleInstance) :
    60 ≤ unsplittableCost counterexampleInstance q := by
  have count := boundedRoutingHasTwoPaid q bound
  have countQ : (2 : ℚ) ≤ (paidCount q : ℚ) := by
    exact_mod_cast count
  rw [unsplittableCostEqPaidCount]
  linarith
end DinitzGargGoemans
