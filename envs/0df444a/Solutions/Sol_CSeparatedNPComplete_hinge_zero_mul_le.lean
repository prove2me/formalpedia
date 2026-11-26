-- Prove2me | solution 1 for CSeparatedNPComplete.hinge_zero_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:58:00.371828+00:00
-- url     : https://prove2.me/submissions/163fb054-f649-4778-961f-dc1cc0b9af22

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Theorems.Thm_CSeparatedNPComplete_hinge_eq_zero_iff

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {c D S : ℝ} (hS : 0 < S)
    (h : hinge c D S = 0) : c * S ≤ D := (hinge_eq_zero_iff hS).mp h
end CSeparatedNPComplete
