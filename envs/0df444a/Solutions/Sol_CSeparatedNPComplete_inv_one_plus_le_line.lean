-- Prove2me | solution 1 for CSeparatedNPComplete.inv_one_plus_le_line
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:48:53.214896+00:00
-- url     : https://prove2.me/submissions/3d2ce2d0-963e-45c0-83c8-56682ee797b6

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_Reciprocal

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
    (1 + x)⁻¹ ≤ 1 - x / 2 := by
  rw [← one_div, div_le_iff₀ (by linarith : 0 < 1 + x)]
  nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
end CSeparatedNPComplete
