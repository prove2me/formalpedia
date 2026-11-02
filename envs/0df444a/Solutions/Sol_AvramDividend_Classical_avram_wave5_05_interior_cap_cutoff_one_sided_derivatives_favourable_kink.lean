-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_05_interior_cap_cutoff_one_sided_derivatives_favourable_kink
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:57:33.423653+00:00
-- url     : https://prove2.me/submissions/0ada257e-4be0-4f6c-9e9d-79f1ed0c51ed

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-!
At a strictly interior cutoff b<c, the slope-one continuation has
ordinary one-sided derivatives w'(b) from the left and 1 from the
right. Its finite kink coefficient 1-w'(b) is nonpositive when
w'(b)>=1. No derivative at the *actual cap* c is assumed.
-/

/-- Exact interior-cutoff one-sided derivative data and favourable kink
    sign, usable in piecewise Ito-Meyer approximations. -/
theorem solution
    (w : ℝ → ℝ) (b : ℝ)
    (hw_diff : DifferentiableAt ℝ w b)
    (hSlope : 1 ≤ deriv w b) :
    HasDerivWithinAt
      (fun y : ℝ => if y ≤ b then w y else w b + (y - b))
      (deriv w b) (Iic b) b ∧
    HasDerivWithinAt
      (fun y : ℝ => if y ≤ b then w y else w b + (y - b))
      1 (Ici b) b ∧
    1 - deriv w b ≤ 0 := by
  have hLeftEq :
      (fun y : ℝ => if y ≤ b then w y else w b + (y - b)) =ᶠ[𝓝[Iic b] b] w := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [mem_Iic] at hy
    simp [hy]
  have hRightEq :
      (fun y : ℝ => if y ≤ b then w y else w b + (y - b)) =ᶠ[𝓝[Ici b] b]
        (fun y : ℝ => w b + (y - b)) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [mem_Ici] at hy
    by_cases hyb : y ≤ b
    · have hyEq : y = b := le_antisymm hyb hy
      subst y
      simp
    · simp [hyb]
  have hLeft : HasDerivWithinAt
      (fun y : ℝ => if y ≤ b then w y else w b + (y - b))
      (deriv w b) (Iic b) b :=
    hw_diff.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
      hLeftEq (by simp)
  have hLin : HasDerivAt (fun y : ℝ => w b + (y - b)) 1 b := by
    simpa using ((hasDerivAt_id b).sub_const b).const_add (w b)
  have hRight : HasDerivWithinAt
      (fun y : ℝ => if y ≤ b then w y else w b + (y - b))
      1 (Ici b) b :=
    hLin.hasDerivWithinAt.congr_of_eventuallyEq_of_mem hRightEq (by simp)
  exact ⟨hLeft, hRight, sub_nonpos.mpr hSlope⟩
