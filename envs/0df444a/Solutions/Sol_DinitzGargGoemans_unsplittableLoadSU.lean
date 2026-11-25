-- Prove2me | solution 1 for DinitzGargGoemans.unsplittableLoadSU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:58:52.964557+00:00
-- url     : https://prove2.me/submissions/2a8284fe-899f-4189-a17c-98409c9915c3

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
    unsplittableLoad counterexampleInstance q .sU =
      (if q .one = .free then 15 else 0) +
        (if q .two = .free then 10 else 0) + 15 := by
  cases h1 : q .one <;> cases h2 : q .two <;> cases h3 : q .three <;>
    simp [unsplittableLoad, counterexampleInstance, counterexampleUses,
      routeEdges, demandAmount, h1, h2, h3, Finset.sum_insert]
  all_goals norm_num
end DinitzGargGoemans
