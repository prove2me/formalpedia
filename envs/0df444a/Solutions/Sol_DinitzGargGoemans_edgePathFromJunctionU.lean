-- Prove2me | solution 1 for DinitzGargGoemans.edgePathFromJunctionU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:03:59.770592+00:00
-- url     : https://prove2.me/submissions/9fe800a0-612f-4d58-85d9-0b6e19ec446d

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
import Theorems.Thm_DinitzGargGoemans_univCommodity
import Theorems.Thm_DinitzGargGoemans_univRouteChoice
import Theorems.Thm_DinitzGargGoemans_univArc
import Theorems.Thm_DinitzGargGoemans_edgePathFromTerminal3
import Theorems.Thm_DinitzGargGoemans_edgePathFromJunctionV
attribute [local simp] DinitzGargGoemans.univCommodity
attribute [local simp] DinitzGargGoemans.univRouteChoice
attribute [local simp] DinitzGargGoemans.univArc

set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans
namespace DinitzGargGoemans
theorem _root_.solution (as : List Arc) (v : Vertex) :
    edgePath .junctionU as v ↔
      (as = [] ∧ v = .junctionU) ∨
      (as = [.uV] ∧ v = .junctionV) ∨
      (as = [.uT3] ∧ v = .terminal3) ∨
      (as = [.uV, .vT1] ∧ v = .terminal1) ∨
      (as = [.uV, .vW] ∧ v = .junctionW) ∨
      (as = [.uV, .vW, .wT2] ∧ v = .terminal2) ∨
      (as = [.uV, .vW, .wT3] ∧ v = .terminal3) := by
  cases as with
  | nil => simpa [edgePath] using (eq_comm : (.junctionU = v ↔ v = .junctionU))
  | cons a rest =>
    cases a <;>
      simp [edgePath, arcTail, arcHead, edgePathFromTerminal3,
        edgePathFromJunctionV]
end DinitzGargGoemans
