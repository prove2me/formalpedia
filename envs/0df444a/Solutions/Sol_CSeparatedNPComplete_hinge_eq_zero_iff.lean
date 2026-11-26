-- Prove2me | solution 1 for CSeparatedNPComplete.hinge_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:47:46.175877+00:00
-- url     : https://prove2.me/submissions/033fd902-c078-4950-b752-32cc9dbd0311

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {c D S : ℝ} (hS : 0 < S) :
    hinge c D S = 0 ↔ c * S ≤ D := by
  simp only [hinge, max_eq_left_iff, sub_nonpos, le_div_iff₀ hS]
end CSeparatedNPComplete
