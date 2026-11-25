-- Prove2me | solution 1 for DinitzGargGoemans.unsplittableLoadVW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:59:03.408431+00:00
-- url     : https://prove2.me/submissions/202445b4-ee86-4c3b-9ad4-245e7f37ad6a

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
    unsplittableLoad counterexampleInstance q .vW =
      (if q .two = .free then 10 else 0) +
        (if q .three = .free then 15 else 0) := by
  cases h1 : q .one <;> cases h2 : q .two <;> cases h3 : q .three <;>
    simp [unsplittableLoad, counterexampleInstance, counterexampleUses,
      routeEdges, demandAmount, h1, h2, h3, Finset.sum_insert]
end DinitzGargGoemans
