-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceSecondBranch_cubic_central_window_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/7763fe78-2959-4bad-95f4-2ece581d8875

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_upperSaddleThirdMoment_le_variance
import Theorems.Thm_CohnElkies_saddleSourceSecondBranchVarianceFloor_pos
import Theorems.Thm_CohnElkies_eventually_saddleSourceGaussianVariance_secondBranch_floor
import Theorems.Thm_CohnElkies_saddleSource_cubic_window_le_of_variance_floor
import Theorems.Thm_CohnElkies_saddleSource_central_rpow_cube_div_sqrt

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 1 ≤ ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          ∀ T : ℝ,
            |T| ≤
              saddleSourceSecondBranchCentralRadius ε ℓ (1 + δ) →
            (ℓ * upperSaddleThirdMoment ε ℓ δ / 6) *
                |T| ^ 3 ≤
              ((2 + (100 / 99 : ℝ) *
                  upperSaddleShellThirdCoefficient ε) /
                (6 * Real.sqrt
                  (saddleSourceSecondBranchVarianceFloor ε))) *
                ℓ ^ (-(1 / 4 : ℝ)) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upper_shortCutoff_le_shortEndpoint,
    eventually_saddleSourceGaussianVariance_secondBranch_floor,
    eventually_upperSaddleThirdMoment_le_variance]
    with ε hε horder hfloor hmoment
  change 0 < ε at hε
  intro ℓ hℓ δ hδ T hT
  have hℓpositive : 0 < ℓ := by linarith
  have hfloorpositive :=
    saddleSourceSecondBranchVarianceFloor_pos hε
  have hvariance := hfloor ℓ hℓpositive δ hδ
  have hcut : 0 < shortCutoff ε := by
    unfold shortCutoff
    positivity
  have hA : 0 ≤ shortEndpoint ε :=
    (hcut.trans_le horder).le
  have hB : 0 ≤ shellLocation ε := by
    unfold shellLocation
    positivity
  have hC :
      0 ≤ 2 + (100 / 99 : ℝ) *
        upperSaddleShellThirdCoefficient ε := by
    unfold upperSaddleShellThirdCoefficient
    positivity
  have hthird := hmoment ℓ hℓ δ hδ
  have hargument : 1 + δ - 1 = δ := by ring
  have hthird' :
      upperSaddleThirdMoment ε ℓ δ ≤
        (2 + (100 / 99 : ℝ) *
          upperSaddleShellThirdCoefficient ε) *
          saddleSourceGaussianVariance ε ℓ (1 + δ) := by
    simpa [saddleSourceGaussianVariance, hargument] using! hthird
  have hbase := saddleSource_cubic_window_le_of_variance_floor
    (ℓ := ℓ)
    (V := saddleSourceGaussianVariance ε ℓ (1 + δ))
    (M := upperSaddleThirdMoment ε ℓ δ)
    (C := 2 + (100 / 99 : ℝ) *
      upperSaddleShellThirdCoefficient ε)
    (V₀ := saddleSourceSecondBranchVarianceFloor ε)
    (z := ℓ ^ (1 / 12 : ℝ))
    (T := T)
    hℓpositive hfloorpositive hvariance hC
    (Real.rpow_nonneg hℓpositive.le _)
    hthird' (by
      simpa [saddleSourceSecondBranchCentralRadius] using! hT)
  calc
    (ℓ * upperSaddleThirdMoment ε ℓ δ / 6) *
        |T| ^ 3 ≤
      ((2 + (100 / 99 : ℝ) *
          upperSaddleShellThirdCoefficient ε) / 6) *
        (ℓ ^ (1 / 12 : ℝ)) ^ 3 /
          (Real.sqrt ℓ *
            Real.sqrt (saddleSourceSecondBranchVarianceFloor ε)) :=
      hbase
    _ = ((2 + (100 / 99 : ℝ) *
          upperSaddleShellThirdCoefficient ε) /
            (6 * Real.sqrt
              (saddleSourceSecondBranchVarianceFloor ε))) *
          (((ℓ ^ (1 / 12 : ℝ)) ^ 3) /
            Real.sqrt ℓ) := by
      ring
    _ = ((2 + (100 / 99 : ℝ) *
          upperSaddleShellThirdCoefficient ε) /
            (6 * Real.sqrt
              (saddleSourceSecondBranchVarianceFloor ε))) *
          ℓ ^ (-(1 / 4 : ℝ)) := by
      rw [saddleSource_central_rpow_cube_div_sqrt hℓpositive]
end CohnElkies
