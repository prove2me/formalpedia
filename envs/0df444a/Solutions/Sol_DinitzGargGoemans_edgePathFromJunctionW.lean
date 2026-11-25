-- Prove2me | solution 1 for DinitzGargGoemans.edgePathFromJunctionW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:57:50.889841+00:00
-- url     : https://prove2.me/submissions/76cd9c45-a6dd-4532-a8e0-0a9bcbeac486

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
import Theorems.Thm_DinitzGargGoemans_univCommodity
import Theorems.Thm_DinitzGargGoemans_univRouteChoice
import Theorems.Thm_DinitzGargGoemans_univArc
import Theorems.Thm_DinitzGargGoemans_edgePathFromTerminal2
import Theorems.Thm_DinitzGargGoemans_edgePathFromTerminal3
attribute [local simp] DinitzGargGoemans.univCommodity
attribute [local simp] DinitzGargGoemans.univRouteChoice
attribute [local simp] DinitzGargGoemans.univArc

set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans
namespace DinitzGargGoemans
theorem _root_.solution (as : List Arc) (v : Vertex) :
    edgePath .junctionW as v ↔
      (as = [] ∧ v = .junctionW) ∨
      (as = [.wT2] ∧ v = .terminal2) ∨
      (as = [.wT3] ∧ v = .terminal3) := by
  cases as with
  | nil => simpa [edgePath] using (eq_comm : (.junctionW = v ↔ v = .junctionW))
  | cons a rest =>
    cases a <;>
      simp [edgePath, arcTail, arcHead, edgePathFromTerminal2,
        edgePathFromTerminal3]
end DinitzGargGoemans
