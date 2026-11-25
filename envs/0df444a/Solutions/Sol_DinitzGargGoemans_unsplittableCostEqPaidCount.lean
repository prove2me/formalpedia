-- Prove2me | solution 1 for DinitzGargGoemans.unsplittableCostEqPaidCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:55:05.143708+00:00
-- url     : https://prove2.me/submissions/1b55b70a-68d5-4d68-bfe9-1232104d9b40

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
import Theorems.Thm_DinitzGargGoemans_univCommodity
import Theorems.Thm_DinitzGargGoemans_univRouteChoice
import Theorems.Thm_DinitzGargGoemans_univArc
attribute [local simp] DinitzGargGoemans.univCommodity
attribute [local simp] DinitzGargGoemans.univRouteChoice
attribute [local simp] DinitzGargGoemans.univArc

set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans
namespace DinitzGargGoemans
theorem _root_.solution (q : Commodity → RouteChoice) :
    unsplittableCost counterexampleInstance q = 30 * paidCount q := by
  cases h1 : q .one <;> cases h2 : q .two <;> cases h3 : q .three <;>
    simp [unsplittableCost, unsplittableLoad, counterexampleInstance,
      counterexampleUses, routeEdges, demandAmount, arcCost, h1, h2, h3,
      paidCount, Finset.sum_insert]
  all_goals norm_num
end DinitzGargGoemans
