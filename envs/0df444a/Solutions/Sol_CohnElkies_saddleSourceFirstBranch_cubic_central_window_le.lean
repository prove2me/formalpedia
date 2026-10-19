-- Prove2me | solution 1 for CohnElkies.saddleSourceFirstBranch_cubic_central_window_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/28d58f00-f4c0-40b2-899d-fe9eb947f53a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperFirstBranch_saddleSourceThirdMoment_scaled_le
import Theorems.Thm_CohnElkies_saddleSource_central_rpow_cube_div_sqrt
import Theorems.Thm_CohnElkies_saddleSource_scaled_cubic_window_le
import Theorems.Thm_CohnElkies_upperFirstBranch_saddleSourceGaussianVariance_scaled_lower_bound
import Theorems.Thm_CohnElkies_saddleSourceFirstBranchThirdMomentCoefficient_pos

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u T : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a)
    (hscale : 1 ≤ ℓ * (1 + u))
    (hT : |T| ≤ saddleSourceFirstBranchCentralRadius ε ℓ u) :
    (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤
      (saddleSourceFirstBranchThirdMomentCoefficient ε /
        (12 * ε * Real.sqrt (2 * ε))) *
          (ℓ * (1 + u)) ^ (-(1 / 4 : ℝ)) := by
  have hη : 0 < 1 + u := by linarith
  have hx : 0 < ℓ * (1 + u) := mul_pos hℓ hη
  have hK :=
    saddleSourceFirstBranchThirdMomentCoefficient_pos hε horder
  have hmoment := upperFirstBranch_saddleSourceThirdMoment_scaled_le
    hε hεsmall hℓ hulower huupper horder hmargin hscale
  have hvariance :=
    upperFirstBranch_saddleSourceGaussianVariance_scaled_lower_bound
      hε hεsmall hℓ hulower huupper horder hmargin
  have hcentral := saddleSource_scaled_cubic_window_le
    (ℓ := ℓ) (η := 1 + u)
    (V := saddleSourceGaussianVariance ε ℓ u)
    (M := upperSaddleThirdMoment ε ℓ (u - 1))
    (K := saddleSourceFirstBranchThirdMomentCoefficient ε)
    (c := 2 * ε)
    (z := (ℓ * (1 + u)) ^ (1 / 12 : ℝ))
    (T := T) hℓ hη (by positivity) hK.le
    (Real.rpow_nonneg hx.le _)
    hmoment hvariance (by
      simpa [saddleSourceFirstBranchCentralRadius] using! hT)
  calc
    (ℓ * upperSaddleThirdMoment ε ℓ (u - 1) / 6) *
        |T| ^ 3 ≤
      (saddleSourceFirstBranchThirdMomentCoefficient ε /
          (6 * (2 * ε) * Real.sqrt (2 * ε))) *
        (((ℓ * (1 + u)) ^ (1 / 12 : ℝ)) ^ 3 /
          Real.sqrt (ℓ * (1 + u))) := hcentral
    _ = (saddleSourceFirstBranchThirdMomentCoefficient ε /
        (12 * ε * Real.sqrt (2 * ε))) *
          (ℓ * (1 + u)) ^ (-(1 / 4 : ℝ)) := by
      rw [saddleSource_central_rpow_cube_div_sqrt hx]
      ring
end CohnElkies
