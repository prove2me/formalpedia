-- Prove2me | solution 1 for CohnElkies.upperGammaThirdMoment_le_two_mul_variance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:27.275309+00:00
-- url     : https://prove2.me/submissions/5af971e4-7a16-4824-b74f-dd140e7f7d5f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperGammaVariance_bounds
import Theorems.Thm_CohnElkies_upperGammaThirdMoment_bounds

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
    {ℓ η : ℝ} (hℓ : 1 ≤ ℓ) (hη : 2 ≤ η) :
    upperGammaThirdMoment ℓ η ≤
      2 * upperGammaVariance ℓ η := by
  have hℓpositive : 0 < ℓ := by linarith
  have hηpositive : 0 < η := by linarith
  have hγthird :=
    (upperGammaThirdMoment_bounds hℓpositive hηpositive).2
  have hγvariance :=
    (upperGammaVariance_bounds hℓpositive hηpositive).1
  have hfirst :
      1 / (2 * η ^ 2) ≤ 1 / (2 * η) := by
    apply (div_le_div_iff₀
      (show 0 < 2 * η ^ 2 by positivity)
      (show 0 < 2 * η by positivity)).2
    nlinarith [mul_nonneg hηpositive.le
      (show 0 ≤ η - 1 by linarith)]
  have hηsquare : 4 ≤ η ^ 2 := by
    nlinarith [sq_nonneg (η - 2)]
  have hsquare : 4 ≤ ℓ * η ^ 2 := by
    calc
      (4 : ℝ) ≤ η ^ 2 := hηsquare
      _ ≤ ℓ * η ^ 2 := by
        nlinarith [mul_nonneg
          (show 0 ≤ ℓ - 1 by linarith)
          (sq_nonneg η)]
  have hsecond :
      2 / (ℓ * η ^ 3) ≤ 1 / (2 * η) := by
    apply (div_le_div_iff₀
      (show 0 < ℓ * η ^ 3 by positivity)
      (show 0 < 2 * η by positivity)).2
    have hscaled :=
      mul_le_mul_of_nonneg_right hsquare hηpositive.le
    nlinarith
  calc
    upperGammaThirdMoment ℓ η ≤
        1 / (2 * η ^ 2) +
          2 / (ℓ * η ^ 3) := hγthird
    _ ≤ 2 * (1 / (2 * η)) := by
      linarith
    _ ≤ 2 * upperGammaVariance ℓ η := by
      linarith
end CohnElkies
