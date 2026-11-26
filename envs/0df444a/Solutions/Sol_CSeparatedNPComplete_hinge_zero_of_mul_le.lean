-- Prove2me | solution 1 for CSeparatedNPComplete.hinge_zero_of_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:58:15.051867+00:00
-- url     : https://prove2.me/submissions/de6e244d-f3e6-4d6c-b8eb-c539ba0a37d0

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
    (h : c * S ≤ D) : hinge c D S = 0 := (hinge_eq_zero_iff hS).mpr h
end CSeparatedNPComplete
