-- Prove2me | solution 1 for CohnElkies.saddleSourceFirstBranch_central_radius_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/7d0fcef6-d51b-42ad-a7cf-2abc1429cd65

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleSource_central_rpow_div_sqrt
import Theorems.Thm_CohnElkies_upperFirstBranch_saddleSourceGaussianVariance_scaled_lower_bound
import Theorems.Thm_CohnElkies_saddleSource_scaled_central_radius_le

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
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a) :
    saddleSourceFirstBranchCentralRadius ε ℓ u ≤
      ((2 + ε / 2) / Real.sqrt (2 * ε)) *
        (ℓ * (1 + u)) ^ (-(5 / 12 : ℝ)) := by
  have hη : 0 < 1 + u := by linarith
  have hx : 0 < ℓ * (1 + u) := mul_pos hℓ hη
  have hvariance :=
    upperFirstBranch_saddleSourceGaussianVariance_scaled_lower_bound
      hε hεsmall hℓ hulower huupper horder hmargin
  have hbase := saddleSource_scaled_central_radius_le
    (ℓ := ℓ) (η := 1 + u)
    (V := saddleSourceGaussianVariance ε ℓ u)
    (c := 2 * ε) (U := 2 + ε / 2)
    (z := (ℓ * (1 + u)) ^ (1 / 12 : ℝ))
    hℓ hη (by positivity) (by linarith)
    (Real.rpow_nonneg hx.le _) hvariance
  calc
    saddleSourceFirstBranchCentralRadius ε ℓ u ≤
      ((2 + ε / 2) / Real.sqrt (2 * ε)) *
        ((ℓ * (1 + u)) ^ (1 / 12 : ℝ) /
          Real.sqrt (ℓ * (1 + u))) := by
      simpa [saddleSourceFirstBranchCentralRadius] using! hbase
    _ = ((2 + ε / 2) / Real.sqrt (2 * ε)) *
        (ℓ * (1 + u)) ^ (-(5 / 12 : ℝ)) := by
      rw [saddleSource_central_rpow_div_sqrt hx]
end CohnElkies
