-- Prove2me | solution 1 for DinitzGargGoemans.edgePathFromJunctionV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:01:12.145453+00:00
-- url     : https://prove2.me/submissions/a59fd48d-1696-4593-ada8-3af73ab56939

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
import Theorems.Thm_DinitzGargGoemans_univCommodity
import Theorems.Thm_DinitzGargGoemans_univRouteChoice
import Theorems.Thm_DinitzGargGoemans_univArc
import Theorems.Thm_DinitzGargGoemans_edgePathFromTerminal1
import Theorems.Thm_DinitzGargGoemans_edgePathFromJunctionW
attribute [local simp] DinitzGargGoemans.univCommodity
attribute [local simp] DinitzGargGoemans.univRouteChoice
attribute [local simp] DinitzGargGoemans.univArc

set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans
namespace DinitzGargGoemans
theorem _root_.solution (as : List Arc) (v : Vertex) :
    edgePath .junctionV as v ↔
      (as = [] ∧ v = .junctionV) ∨
      (as = [.vT1] ∧ v = .terminal1) ∨
      (as = [.vW] ∧ v = .junctionW) ∨
      (as = [.vW, .wT2] ∧ v = .terminal2) ∨
      (as = [.vW, .wT3] ∧ v = .terminal3) := by
  cases as with
  | nil => simpa [edgePath] using (eq_comm : (.junctionV = v ↔ v = .junctionV))
  | cons a rest =>
    cases a <;>
      simp [edgePath, arcTail, arcHead, edgePathFromTerminal1,
        edgePathFromJunctionW]
end DinitzGargGoemans
