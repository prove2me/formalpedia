-- Prove2me | solution 1 for DinitzGargGoemans.boundedRoutingHasTwoPaid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:58:58.279184+00:00
-- url     : https://prove2.me/submissions/ec1c8497-3ee4-4c15-86f0-a0217a6cb1e9

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
import Theorems.Thm_DinitzGargGoemans_univCommodity
import Theorems.Thm_DinitzGargGoemans_univRouteChoice
import Theorems.Thm_DinitzGargGoemans_univArc
import Theorems.Thm_DinitzGargGoemans_counterexampleMaximumDemand
import Theorems.Thm_DinitzGargGoemans_fractionalLoadEqCapacity
attribute [local simp] DinitzGargGoemans.univCommodity
attribute [local simp] DinitzGargGoemans.univRouteChoice
attribute [local simp] DinitzGargGoemans.univArc

set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans
namespace DinitzGargGoemans
theorem _root_.solution (q : Commodity → RouteChoice)
    (bound : ∀ a,
      unsplittableLoad counterexampleInstance q a ≤
        fractionalLoad counterexampleInstance splitFlow a +
          maximumDemand counterexampleInstance) :
    2 ≤ paidCount q := by
  have hsu := bound .sU
  have huv := bound .uV
  have hvw := bound .vW
  simp only [fractionalLoadEqCapacity, counterexampleMaximumDemand] at hsu huv hvw
  cases h1 : q .one <;> cases h2 : q .two <;> cases h3 : q .three <;>
    simp [unsplittableLoad, counterexampleInstance, counterexampleUses,
      routeEdges, demandAmount, arcCapacity, paidCount, h1, h2, h3,
      Finset.sum_insert] at hsu huv hvw ⊢
  all_goals linarith
end DinitzGargGoemans
