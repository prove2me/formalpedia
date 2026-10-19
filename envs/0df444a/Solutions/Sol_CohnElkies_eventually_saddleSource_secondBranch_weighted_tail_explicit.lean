-- Prove2me | solution 1 for CohnElkies.eventually_saddleSource_secondBranch_weighted_tail_explicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/b878fdde-4f1f-44de-8242-87ac32a08b74

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_eventually_saddleSourceGaussianVariance_secondBranch_pos
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_nonneg
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_mul_gaussian_integrable
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_mul_exp_abs_integrable
import Theorems.Thm_CohnElkies_saddleGaussianTailSet_measurable
import Theorems.Thm_CohnElkies_saddleGaussian_cubic_tail_integral_le
import Theorems.Thm_CohnElkies_eventually_saddleSource_secondBranch_weighted_integrable
import Theorems.Thm_CohnElkies_saddleGaussian_weighted_integral_le_rescaled
import Theorems.Thm_CohnElkies_saddleExponential_weighted_integral_le_rescaled
import Theorems.Thm_CohnElkies_eventually_saddleSource_secondBranch_pointwise_gaussian_plus_outer

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
          ∀ R : ℝ, 0 ≤ R →
            6 ≤ saddleSourceSecondBranchGaussianRate ε ℓ δ →
              (∫ T : ℝ in saddleGaussianTailSet R,
                saddleGaussianTailWeight T *
                  Real.exp
                    (-saddleSourceContourDamping
                      ε ℓ (1 + δ) T)) ≤
                2 * Real.exp
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
                            ℓ / 2))) := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_saddleSource_secondBranch_weighted_integrable,
      eventually_saddleSource_secondBranch_pointwise_gaussian_plus_outer,
      eventually_saddleSourceGaussianVariance_secondBranch_pos]
    with ε hε hsource hpoint hvariance
  change 0 < ε at hε
  intro ℓ hℓ δ hδ R hR hk
  let k : ℝ := saddleSourceSecondBranchGaussianRate ε ℓ δ
  let q : ℝ := saddleSourceSecondBranchGammaGaussianRate ℓ δ
  let a : ℝ := saddleSourceSecondBranchGammaLinearRate ℓ
  let b : ℝ := saddleSourceSecondBranchOuterBarrier ε ℓ δ
  have hδ0 : 0 ≤ δ := by nlinarith
  have hη : 0 < 2 + δ := by linarith
  have hV := hvariance ℓ hℓ δ hδ
  have hkpos : 0 < k := by
    try dsimp [k, saddleSourceSecondBranchGaussianRate]
    positivity
  have hq : 0 < q := by
    try dsimp [q, saddleSourceSecondBranchGammaGaussianRate]
    positivity
  have ha : 0 < a := by
    try dsimp [a, saddleSourceSecondBranchGammaLinearRate]
    positivity
  have hactual := hsource ℓ hℓ δ hδ
  have hlocal :=
    saddleGaussianTailWeight_mul_gaussian_integrable hkpos
  have hgamma :=
    saddleGaussianTailWeight_mul_gaussian_integrable hq
  have hlinear :=
    saddleGaussianTailWeight_mul_exp_abs_integrable ha
  have houter : Integrable
      (fun T : ℝ =>
        Real.exp (-b) *
          (saddleGaussianTailWeight T *
            Real.exp (-q * T ^ 2) +
            saddleGaussianTailWeight T *
              Real.exp (-a * |T|))) :=
    (hgamma.add hlinear).const_mul (Real.exp (-b))
  have hmajor : Integrable
      (fun T : ℝ =>
        saddleGaussianTailWeight T *
            Real.exp (-k * T ^ 2) +
          Real.exp (-b) *
            (saddleGaussianTailWeight T *
              Real.exp (-q * T ^ 2) +
              saddleGaussianTailWeight T *
                Real.exp (-a * |T|))) :=
    hlocal.add houter
  have hcompare := MeasureTheory.setIntegral_mono_on
    hactual.integrableOn hmajor.integrableOn
    (saddleGaussianTailSet_measurable R)
    (fun T _ => by
      simpa [k, q, a, b] using!
        hpoint ℓ hℓ δ hδ T)
  have hgaussianTail := saddleGaussian_cubic_tail_integral_le
    (k := k) (R := R) (by simpa [k] using! hk) hR
  have hgammanonnegative :
      0 ≤ᶠ[ae (volume : Measure ℝ)]
        (fun T : ℝ =>
          saddleGaussianTailWeight T *
            Real.exp (-q * T ^ 2)) :=
    Filter.Eventually.of_forall
      (fun T => mul_nonneg
        (saddleGaussianTailWeight_nonneg T)
        (Real.exp_pos _).le)
  have hlinearnonnegative :
      0 ≤ᶠ[ae (volume : Measure ℝ)]
        (fun T : ℝ =>
          saddleGaussianTailWeight T *
            Real.exp (-a * |T|)) :=
    Filter.Eventually.of_forall
      (fun T => mul_nonneg
        (saddleGaussianTailWeight_nonneg T)
        (Real.exp_pos _).le)
  have hgammaTail := MeasureTheory.setIntegral_le_integral
    (s := saddleGaussianTailSet R)
    hgamma hgammanonnegative
  have hlinearTail := MeasureTheory.setIntegral_le_integral
    (s := saddleGaussianTailSet R)
    hlinear hlinearnonnegative
  have hgammaFull :=
    saddleGaussian_weighted_integral_le_rescaled hq
  have hlinearFull :=
    saddleExponential_weighted_integral_le_rescaled ha
  calc
    (∫ T : ℝ in saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
        Real.exp
          (-saddleSourceContourDamping ε ℓ (1 + δ) T)) ≤
      ∫ T : ℝ in saddleGaussianTailSet R,
        (saddleGaussianTailWeight T *
          Real.exp (-k * T ^ 2) +
          Real.exp (-b) *
            (saddleGaussianTailWeight T *
              Real.exp (-q * T ^ 2) +
              saddleGaussianTailWeight T *
                Real.exp (-a * |T|))) := hcompare
    _ = (∫ T : ℝ in saddleGaussianTailSet R,
          saddleGaussianTailWeight T *
            Real.exp (-k * T ^ 2)) +
        Real.exp (-b) *
          ((∫ T : ℝ in saddleGaussianTailSet R,
            saddleGaussianTailWeight T *
              Real.exp (-q * T ^ 2)) +
            ∫ T : ℝ in saddleGaussianTailSet R,
              saddleGaussianTailWeight T *
                Real.exp (-a * |T|)) := by
      rw [MeasureTheory.integral_add
        hlocal.integrableOn houter.integrableOn,
        MeasureTheory.integral_const_mul,
        MeasureTheory.integral_add
          hgamma.integrableOn hlinear.integrableOn]
    _ ≤ 2 * Real.exp (-(k / 4) * R ^ 2) *
          Real.sqrt (Real.pi / (k / 4)) +
        Real.exp (-b) *
          ((∫ T : ℝ,
            saddleGaussianTailWeight T *
              Real.exp (-q * T ^ 2)) +
            ∫ T : ℝ,
              saddleGaussianTailWeight T *
                Real.exp (-a * |T|)) := by
      gcongr
    _ ≤ 2 * Real.exp (-(k / 4) * R ^ 2) *
          Real.sqrt (Real.pi / (k / 4)) +
        Real.exp (-b) *
          (2 * max (1 : ℝ)
            ((Real.sqrt (q / 6) ^ 3)⁻¹) *
              Real.sqrt (Real.pi / (q / 2)) +
            2 * max (1 : ℝ) (((a / 6) ^ 3)⁻¹) *
              (2 / (a / 2))) := by
      gcongr
    _ = _ := by rfl
end CohnElkies
