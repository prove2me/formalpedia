-- Prove2me | solution 1 for DinitzGargGoemans.allSourceTerminalPaths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:06:56.809167+00:00
-- url     : https://prove2.me/submissions/4508bec6-dd93-4848-9a2a-d6e3b3104923

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
import Theorems.Thm_DinitzGargGoemans_univCommodity
import Theorems.Thm_DinitzGargGoemans_univRouteChoice
import Theorems.Thm_DinitzGargGoemans_univArc
import Theorems.Thm_DinitzGargGoemans_edgePathFromSource
attribute [local simp] DinitzGargGoemans.univCommodity
attribute [local simp] DinitzGargGoemans.univRouteChoice
attribute [local simp] DinitzGargGoemans.univArc

set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans
namespace DinitzGargGoemans
theorem _root_.solution (k : Commodity) (as : List Arc) :
    edgePath .source as (commodityTerminal k) ↔
      as = routeEdges k .paid ∨ as = routeEdges k .free := by
  cases k with
  | one =>
    simpa [routeEdges, commodityTerminal] using
      (edgePathFromSource as .terminal1)
  | two =>
    simpa [routeEdges, commodityTerminal] using
      (edgePathFromSource as .terminal2)
  | three =>
    simpa [routeEdges, commodityTerminal] using
      (edgePathFromSource as .terminal3)
end DinitzGargGoemans
