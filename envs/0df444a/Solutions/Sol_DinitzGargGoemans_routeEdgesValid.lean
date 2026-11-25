-- Prove2me | solution 1 for DinitzGargGoemans.routeEdgesValid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:58:49.856818+00:00
-- url     : https://prove2.me/submissions/af6d40a7-1022-46d6-aa25-41de322fd891

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
theorem _root_.solution :
    ∀ k r, edgePath .source (routeEdges k r) (commodityTerminal k) := by
  intro k r
  cases k <;> cases r <;>
    simp [edgePath, routeEdges, commodityTerminal, arcTail, arcHead]
end DinitzGargGoemans
