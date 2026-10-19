-- Prove2me | solution 1 for CohnElkies.eventually_saddleSource_secondBranch_normalized_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/da10cec5-8c2c-4b6f-bdcc-232f8394d24f

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_saddleSourceGaussianVariance_secondBranch_pos
import Theorems.Thm_CohnElkies_eventually_saddleSource_secondBranch_weighted_tail_explicit
import Theorems.Thm_CohnElkies_saddleSourceSecondBranch_normalizedGaussian_prefactor
import Theorems.Thm_CohnElkies_saddleSourceSecondBranch_normalizedGaussian_exponent

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
          ∀ z : ℝ, 0 ≤ z →
            6 ≤ saddleSourceSecondBranchGaussianRate ε ℓ δ →
              Real.sqrt
                  (ℓ * saddleSourceGaussianVariance
                    ε ℓ (1 + δ)) *
                (∫ T : ℝ in saddleGaussianTailSet
                    (z / Real.sqrt
                      (ℓ * saddleSourceGaussianVariance
                        ε ℓ (1 + δ))),
                  saddleGaussianTailWeight T *
                    Real.exp
                      (-saddleSourceContourDamping
                        ε ℓ (1 + δ) T)) ≤
                2 * Real.sqrt (400 * Real.exp 1 * Real.pi) *
                  Real.exp
                    (-(z ^ 2 / (400 * Real.exp 1))) +
                Real.sqrt
                    (ℓ * saddleSourceGaussianVariance
                      ε ℓ (1 + δ)) *
                  Real.exp
                    (-saddleSourceSecondBranchOuterBarrier
                      ε ℓ δ) *
                    (2 * max (1 : ℝ)
                      ((Real.sqrt
                        (saddleSourceSecondBranchGammaGaussianRate
                          ℓ δ / 6) ^ 3)⁻¹) *
                        Real.sqrt
                          (Real.pi /
                            (saddleSourceSecondBranchGammaGaussianRate
                              ℓ δ / 2)) +
                      2 * max (1 : ℝ)
                        (((saddleSourceSecondBranchGammaLinearRate
                          ℓ / 6) ^ 3)⁻¹) *
                          (2 /
                            (saddleSourceSecondBranchGammaLinearRate
                              ℓ / 2))) := by
  filter_upwards
    [eventually_saddleSource_secondBranch_weighted_tail_explicit,
      eventually_saddleSourceGaussianVariance_secondBranch_pos]
    with ε htail hvariance
  intro ℓ hℓ δ hδ z hz hk
  let V : ℝ := saddleSourceGaussianVariance ε ℓ (1 + δ)
  let R : ℝ := z / Real.sqrt (ℓ * V)
  have hV : 0 < V := hvariance ℓ hℓ δ hδ
  have hR : 0 ≤ R := by
    try dsimp [R]
    positivity
  have hsource := htail ℓ hℓ δ hδ R hR hk
  have hpref := saddleSourceSecondBranch_normalizedGaussian_prefactor
    hℓ hV
  have hexponent :=
    saddleSourceSecondBranch_normalizedGaussian_exponent
      (z := z) hℓ hV
  have hs : 0 ≤ Real.sqrt (ℓ * V) :=
    Real.sqrt_nonneg _
  calc
    Real.sqrt
        (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ)) *
      (∫ T : ℝ in saddleGaussianTailSet
          (z / Real.sqrt
            (ℓ * saddleSourceGaussianVariance ε ℓ (1 + δ))),
        saddleGaussianTailWeight T *
          Real.exp
            (-saddleSourceContourDamping ε ℓ (1 + δ) T)) ≤
      Real.sqrt (ℓ * V) *
        (2 * Real.exp
            (-(saddleSourceSecondBranchGaussianRate
              ε ℓ δ / 4) * R ^ 2) *
              Real.sqrt
                (Real.pi /
                  (saddleSourceSecondBranchGaussianRate
                    ε ℓ δ / 4)) +
          Real.exp
              (-saddleSourceSecondBranchOuterBarrier
                ε ℓ δ) *
            (2 * max (1 : ℝ)
              ((Real.sqrt
                (saddleSourceSecondBranchGammaGaussianRate
                  ℓ δ / 6) ^ 3)⁻¹) *
                Real.sqrt
                  (Real.pi /
                    (saddleSourceSecondBranchGammaGaussianRate
                      ℓ δ / 2)) +
              2 * max (1 : ℝ)
                (((saddleSourceSecondBranchGammaLinearRate
                  ℓ / 6) ^ 3)⁻¹) *
                  (2 /
                    (saddleSourceSecondBranchGammaLinearRate
                      ℓ / 2)))) := by
        change Real.sqrt (ℓ * V) *
          (∫ T : ℝ in saddleGaussianTailSet R,
            saddleGaussianTailWeight T *
              Real.exp
                (-saddleSourceContourDamping
                  ε ℓ (1 + δ) T)) ≤ _
        exact mul_le_mul_of_nonneg_left hsource hs
    _ = _ := by
      have hexponent' :
          (saddleSourceSecondBranchGaussianRate
            ε ℓ δ / 4) *
            (z / Real.sqrt (ℓ * V)) ^ 2 =
              z ^ 2 / (400 * Real.exp 1) := by
        simpa [V] using! hexponent
      have hnegative :
          -(saddleSourceSecondBranchGaussianRate
            ε ℓ δ / 4) *
            (z / Real.sqrt (ℓ * V)) ^ 2 =
              -(z ^ 2 / (400 * Real.exp 1)) := by
        linarith
      have hpref' :
          Real.sqrt (ℓ * V) *
            Real.sqrt
              (Real.pi /
                (saddleSourceSecondBranchGaussianRate
                  ε ℓ δ / 4)) =
            Real.sqrt (400 * Real.exp 1 * Real.pi) := by
        simpa [V] using! hpref
      try dsimp [R]
      rw [hnegative]
      have hscaled := congrArg
        (fun x : ℝ =>
          2 * Real.exp
            (-(z ^ 2 / (400 * Real.exp 1))) * x)
        hpref'
      nlinarith
end CohnElkies
