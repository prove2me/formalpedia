-- Prove2me | solution 1 for DinitzGargGoemans.edgePathFromTerminal3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:50:42.900111+00:00
-- url     : https://prove2.me/submissions/e4d1f6ad-e4ca-4046-9da6-c44e18167046

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
theorem _root_.solution (as : List Arc) (v : Vertex) :
    edgePath .terminal3 as v ↔ as = [] ∧ v = .terminal3 := by
  cases as with
  | nil => simpa [edgePath] using (eq_comm : (.terminal3 = v ↔ v = .terminal3))
  | cons a rest =>
    cases a <;> simp [edgePath, arcTail]
end DinitzGargGoemans
