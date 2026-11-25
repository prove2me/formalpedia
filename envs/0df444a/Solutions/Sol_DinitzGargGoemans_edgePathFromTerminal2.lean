-- Prove2me | solution 1 for DinitzGargGoemans.edgePathFromTerminal2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:54:09.704861+00:00
-- url     : https://prove2.me/submissions/33604c3f-923a-475f-9a47-8a0a11a990fe

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
    edgePath .terminal2 as v ↔ as = [] ∧ v = .terminal2 := by
  cases as with
  | nil => simpa [edgePath] using (eq_comm : (.terminal2 = v ↔ v = .terminal2))
  | cons a rest =>
    cases a <;> simp [edgePath, arcTail]
end DinitzGargGoemans
