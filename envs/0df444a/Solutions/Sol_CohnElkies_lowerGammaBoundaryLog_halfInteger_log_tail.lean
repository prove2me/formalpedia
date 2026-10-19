-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_halfInteger_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/26919210-bf61-4f9b-b643-465939f3bf55

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lower_sqrtFactor_ge_abs_half
import Theorems.Thm_CohnElkies_lowerCoth_pos
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_halfInteger

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology
namespace CohnElkies
theorem _root_.solution
    (k : ℕ) {R y : ℝ} (hR : 0 < R) (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y ≤
      ((k : ℝ) + 1 / 2) * Real.log
        (2 * Real.pi * R ^ 2 / |y|) +
      (1 / 2 : ℝ) *
        Real.log (lowerCoth (Real.pi * |y| / 2)) := by
  have hyhalf : 0 < |y| / 2 := by positivity
  have hsum :
      (k : ℝ) * Real.log (|y| / 2) ≤
        ∑ j ∈ Finset.range k,
          Real.log
            (Real.sqrt
              (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) := by
    calc
      (k : ℝ) * Real.log (|y| / 2) =
          ∑ j ∈ Finset.range k,
            Real.log (|y| / 2) := by simp
      _ ≤ ∑ j ∈ Finset.range k,
          Real.log
            (Real.sqrt
              (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact Real.log_le_log hyhalf
          (lower_sqrtFactor_ge_abs_half
            ((j : ℝ) + 1 / 2) y)
  have hlogratio :
      Real.log (Real.pi * R ^ 2) - Real.log (|y| / 2) =
        Real.log (2 * Real.pi * R ^ 2 / |y|) := by
    rw [← Real.log_div
      (mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hR.ne'))
      hyhalf.ne']
    congr 1
    field_simp [abs_ne_zero.mpr hy]
  have hcoth : 0 < lowerCoth (Real.pi * |y| / 2) := by
    apply lowerCoth_pos
    positivity
  have hlogcoth :
      Real.log
        (lowerCoth (Real.pi * |y| / 2) / (|y| / 2)) =
      Real.log (lowerCoth (Real.pi * |y| / 2)) -
        Real.log (|y| / 2) :=
    Real.log_div hcoth.ne' hyhalf.ne'
  rw [lowerGammaBoundaryLog_halfInteger k R hy, hlogcoth]
  calc
    ((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log
            (Real.sqrt
              (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) +
        (1 / 2 : ℝ) *
          (Real.log (lowerCoth (Real.pi * |y| / 2)) -
            Real.log (|y| / 2)) ≤
      ((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2) -
        (k : ℝ) * Real.log (|y| / 2) +
        (1 / 2 : ℝ) *
          (Real.log (lowerCoth (Real.pi * |y| / 2)) -
            Real.log (|y| / 2)) := by
      linarith
    _ = ((k : ℝ) + 1 / 2) *
          (Real.log (Real.pi * R ^ 2) -
            Real.log (|y| / 2)) +
          (1 / 2 : ℝ) *
            Real.log (lowerCoth (Real.pi * |y| / 2)) := by
      ring
    _ = ((k : ℝ) + 1 / 2) * Real.log
          (2 * Real.pi * R ^ 2 / |y|) +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |y| / 2)) := by
      rw [hlogratio]
end CohnElkies
