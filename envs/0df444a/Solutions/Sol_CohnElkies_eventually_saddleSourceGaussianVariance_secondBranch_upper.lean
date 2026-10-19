-- Prove2me | solution 1 for CohnElkies.eventually_saddleSourceGaussianVariance_secondBranch_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/3e5eb4af-e3d7-49fc-8541-febcfc6308af

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
      ∀ ℓ : ℝ, 1 ≤ ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          saddleSourceGaussianVariance ε ℓ (1 + δ) ≤
            saddleSourceSecondBranchVarianceCoefficient ε *
              Real.exp
                ((shellLocation ε + 1) * δ) := by
  filter_upwards [self_mem_nhdsWithin,
    eventually_upperSaddleVariance_bounds]
    with ε hε hvariance
  change 0 < ε at hε
  intro ℓ hℓ δ hδ
  have hℓpositive : 0 < ℓ := by linarith
  have hδ0 : 0 ≤ δ := by nlinarith
  let η : ℝ := 2 + δ
  have hηtwo : 2 ≤ η := by
    try dsimp [η]
    linarith
  have hη : 0 < η := by linarith
  have hB : 0 ≤ shellLocation ε := by
    unfold shellLocation
    positivity
  have hexp : 1 ≤
      Real.exp ((shellLocation ε + 1) * δ) := by
    apply (Real.one_le_exp_iff).2
    positivity
  have hfirst : 1 / (2 * η) ≤ (1 : ℝ) := by
    apply (div_le_iff₀
      (show 0 < 2 * η by positivity)).2
    linarith
  have hden : 0 < ℓ * η ^ 2 := by positivity
  have hsecond : 1 / (ℓ * η ^ 2) ≤ (1 : ℝ) := by
    apply (div_le_iff₀ hden).2
    have hηsquare : 1 ≤ η ^ 2 := by
      nlinarith [sq_nonneg (η - 1)]
    have hscaled := mul_le_mul_of_nonneg_right
      hℓ (sq_nonneg η)
    nlinarith
  have hshell :=
    (upperPositiveShellVariance_bounds hε hδ0).2
  have hfull := (hvariance ℓ hℓpositive δ hδ).2
  have hsource :
      saddleSourceGaussianVariance ε ℓ (1 + δ) ≤
        1 / (2 * η) + 1 / (ℓ * η ^ 2) +
          upperPositiveShellVariance ε δ := by
    simpa [saddleSourceGaussianVariance, η] using! hfull
  have hshell' :
      upperPositiveShellVariance ε δ ≤
        (shellLocation ε + 1) ^ 2 *
          shellWeight ε *
            Real.exp ((shellLocation ε + 1) * δ) := by
    convert! hshell using 1; ring_nf
  unfold saddleSourceSecondBranchVarianceCoefficient
  nlinarith
end CohnElkies
