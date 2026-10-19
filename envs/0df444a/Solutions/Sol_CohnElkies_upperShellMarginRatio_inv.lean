-- Prove2me | solution 1 for CohnElkies.upperShellMarginRatio_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:26.273981+00:00
-- url     : https://prove2.me/submissions/f5ef3aaa-6b50-43f4-b9c0-3784d3c3a603

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {x : ℝ} (hx : x ≠ 0) :
    upperShellMarginRatio x⁻¹ =
      5000 * (10 * Real.log x + x ^ 3) *
        Real.exp (-(x ^ 2) / 8) *
          Real.exp (5 * Real.log x / x) := by
  have hshort : shortEndpoint x⁻¹ = 10 * Real.log x := by
    simp [shortEndpoint]
  have hcutoff : (shortCutoff x⁻¹)⁻¹ = x ^ 3 := by
    simp [shortCutoff]
  have hlocation : shellLocation x⁻¹ = x ^ 3 := by
    simp [shellLocation]
  have hweight :
      shellWeight x⁻¹ = Real.exp (-(3 : ℝ) * x ^ 2 / 8) := by
    unfold shellWeight
    rw [hlocation]
    congr 1
    field_simp [hx]
  have hexp :
      Real.exp ((x⁻¹ / 2) * (10 * Real.log x)) /
          (Real.exp (-(3 : ℝ) * x ^ 2 / 8) *
            Real.exp ((x⁻¹ / 2) * x ^ 3)) =
        Real.exp (-(x ^ 2) / 8) *
          Real.exp (5 * Real.log x / x) := by
    rw [← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
    congr 1
    field_simp [hx]; ring
  unfold upperShellMarginRatio upperShellShortCoefficient
  rw [hshort, hcutoff, hlocation, hweight]
  calc
    5000 * (10 * Real.log x + x ^ 3) *
        Real.exp (x⁻¹ / 2 * (10 * Real.log x)) /
          (Real.exp (-(3 : ℝ) * x ^ 2 / 8) *
            Real.exp (x⁻¹ / 2 * x ^ 3)) =
      5000 * (10 * Real.log x + x ^ 3) *
        (Real.exp (x⁻¹ / 2 * (10 * Real.log x)) /
          (Real.exp (-(3 : ℝ) * x ^ 2 / 8) *
            Real.exp (x⁻¹ / 2 * x ^ 3))) := by ring
    _ = 5000 * (10 * Real.log x + x ^ 3) *
        (Real.exp (-(x ^ 2) / 8) *
          Real.exp (5 * Real.log x / x)) := by
      rw [hexp]
    _ = 5000 * (10 * Real.log x + x ^ 3) *
        Real.exp (-(x ^ 2) / 8) *
          Real.exp (5 * Real.log x / x) := by ring
end CohnElkies
