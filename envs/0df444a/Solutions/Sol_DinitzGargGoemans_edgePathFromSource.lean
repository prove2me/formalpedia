-- Prove2me | solution 1 for DinitzGargGoemans.edgePathFromSource
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T09:06:20.360749+00:00
-- url     : https://prove2.me/submissions/01350e11-2bbd-40ef-9a59-a2109028e5b2

import Definitions.Def_DinitzGargGoemans_Definitions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_DinitzGargGoemans_Proof
import Theorems.Thm_DinitzGargGoemans_univCommodity
import Theorems.Thm_DinitzGargGoemans_univRouteChoice
import Theorems.Thm_DinitzGargGoemans_univArc
import Theorems.Thm_DinitzGargGoemans_edgePathFromTerminal1
import Theorems.Thm_DinitzGargGoemans_edgePathFromTerminal2
import Theorems.Thm_DinitzGargGoemans_edgePathFromTerminal3
import Theorems.Thm_DinitzGargGoemans_edgePathFromJunctionU
attribute [local simp] DinitzGargGoemans.univCommodity
attribute [local simp] DinitzGargGoemans.univRouteChoice
attribute [local simp] DinitzGargGoemans.univArc

set_option autoImplicit true
open scoped BigOperators
open DinitzGargGoemans
namespace DinitzGargGoemans
theorem _root_.solution (as : List Arc) (v : Vertex) :
    edgePath .source as v ↔
      (as = [] ∧ v = .source) ∨
      (as = [.sT1] ∧ v = .terminal1) ∨
      (as = [.sT2] ∧ v = .terminal2) ∨
      (as = [.sU] ∧ v = .junctionU) ∨
      (as = [.sU, .uV] ∧ v = .junctionV) ∨
      (as = [.sU, .uT3] ∧ v = .terminal3) ∨
      (as = [.sU, .uV, .vT1] ∧ v = .terminal1) ∨
      (as = [.sU, .uV, .vW] ∧ v = .junctionW) ∨
      (as = [.sU, .uV, .vW, .wT2] ∧ v = .terminal2) ∨
      (as = [.sU, .uV, .vW, .wT3] ∧ v = .terminal3) := by
  cases as with
  | nil => simpa [edgePath] using (eq_comm : (.source = v ↔ v = .source))
  | cons a rest =>
    cases a <;>
      simp [edgePath, arcTail, arcHead, edgePathFromTerminal1,
        edgePathFromTerminal2, edgePathFromTerminal3,
        edgePathFromJunctionU]
end DinitzGargGoemans
