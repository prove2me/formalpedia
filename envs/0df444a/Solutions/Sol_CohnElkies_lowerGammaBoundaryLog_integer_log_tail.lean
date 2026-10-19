-- Prove2me | solution 1 for CohnElkies.lowerGammaBoundaryLog_integer_log_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:22.892104+00:00
-- url     : https://prove2.me/submissions/b2634b74-e10f-410d-89e3-a7aa550a4fb5

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerGammaBoundaryLog_integer
import Theorems.Thm_CohnElkies_lower_sqrtFactor_ge_abs_half

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
    lowerGammaBoundaryLog (k : ℝ) R y ≤
      (k : ℝ) * Real.log
        (2 * Real.pi * R ^ 2 / |y|) := by
  have hyhalf : 0 < |y| / 2 := by positivity
  have hsum :
      (k : ℝ) * Real.log (|y| / 2) ≤
        ∑ j ∈ Finset.range k,
          Real.log
            (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2)) := by
    calc
      (k : ℝ) * Real.log (|y| / 2) =
          ∑ j ∈ Finset.range k,
            Real.log (|y| / 2) := by simp
      _ ≤ ∑ j ∈ Finset.range k,
          Real.log
            (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact Real.log_le_log hyhalf
          (lower_sqrtFactor_ge_abs_half (j : ℝ) y)
  have hlogratio :
      Real.log (Real.pi * R ^ 2) - Real.log (|y| / 2) =
        Real.log (2 * Real.pi * R ^ 2 / |y|) := by
    rw [← Real.log_div
      (mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hR.ne'))
      hyhalf.ne']
    congr 1
    field_simp [abs_ne_zero.mpr hy]
  rw [lowerGammaBoundaryLog_integer k R hy]
  calc
    (k : ℝ) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log
            (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2)) ≤
      (k : ℝ) * Real.log (Real.pi * R ^ 2) -
        (k : ℝ) * Real.log (|y| / 2) := by
        linarith
    _ = (k : ℝ) *
        (Real.log (Real.pi * R ^ 2) -
          Real.log (|y| / 2)) := by
      ring
    _ = (k : ℝ) * Real.log
        (2 * Real.pi * R ^ 2 / |y|) := by
      rw [hlogratio]
end CohnElkies
