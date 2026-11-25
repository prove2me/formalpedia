-- Prove2me | solution 1 for DinitzGargGoemans.edgePathFromTerminal1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:50:48.636581+00:00
-- url     : https://prove2.me/submissions/bb8a0e08-406d-43ab-8152-30cb0c664f69

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
    edgePath .terminal1 as v ↔ as = [] ∧ v = .terminal1 := by
  cases as with
  | nil => simpa [edgePath] using (eq_comm : (.terminal1 = v ↔ v = .terminal1))
  | cons a rest =>
    cases a <;> simp [edgePath, arcTail]
end DinitzGargGoemans
