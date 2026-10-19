-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceGaussianVariance_secondBranch_floor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/bda60a52-ff20-4e1e-b4de-0f88eaddff0d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_upperPositiveShellVariance_bounds
import Theorems.Thm_CohnElkies_eventually_upperSaddleVariance_bounds

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
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          saddleSourceSecondBranchVarianceFloor ε ≤
            saddleSourceGaussianVariance ε ℓ (1 + δ) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upperSaddleVariance_bounds]
    with ε hε hvariance
  change 0 < ε at hε
  intro ℓ hℓ δ hδ
  have hδ0 : 0 ≤ δ := by linarith
  have hB : 0 ≤ shellLocation ε := by
    unfold shellLocation
    positivity
  have hfactor :
      0 ≤ (1 / 2 : ℝ) * (shellLocation ε) ^ 2 *
        shellWeight ε := by
    have hweight := shellWeight_pos ε
    positivity
  have hpositive :=
    (upperPositiveShellVariance_bounds hε hδ0).1
  have hfull := (hvariance ℓ hℓ δ hδ).1
  have hmono :
      Real.exp ((ε / 2) * shellLocation ε) ≤
        Real.exp (δ * shellLocation ε) :=
    Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right hδ hB)
  have hfloor :
      saddleSourceSecondBranchVarianceFloor ε ≤
        (99 / 100 : ℝ) *
          upperPositiveShellVariance ε δ := by
    calc
      saddleSourceSecondBranchVarianceFloor ε =
          (99 / 100 : ℝ) *
            ((1 / 2 : ℝ) *
              (shellLocation ε) ^ 2 *
                shellWeight ε *
                  Real.exp ((ε / 2) * shellLocation ε)) := by
        unfold saddleSourceSecondBranchVarianceFloor
        ring
      _ ≤ (99 / 100 : ℝ) *
            ((1 / 2 : ℝ) *
              (shellLocation ε) ^ 2 *
                shellWeight ε *
                  Real.exp (δ * shellLocation ε)) := by
        gcongr
      _ ≤ (99 / 100 : ℝ) *
            upperPositiveShellVariance ε δ := by
        gcongr
  have hη : 0 < 2 + δ := by linarith
  have hgamma : 0 ≤ 1 / (2 * (2 + δ)) := by
    positivity
  unfold saddleSourceGaussianVariance
  have hargument : 1 + δ - 1 = δ := by ring
  rw [hargument]
  linarith
end CohnElkies
