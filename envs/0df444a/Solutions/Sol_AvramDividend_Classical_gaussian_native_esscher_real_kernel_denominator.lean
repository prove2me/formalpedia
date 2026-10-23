-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_native_esscher_real_kernel_denominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T16:17:34.159784+00:00
-- url     : https://prove2.me/submissions/9fd530cc-5060-4ec9-b420-5489968c3b60

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_native_esscher_root_volterra_denominator
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_laplace_real_bridge
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_esscher_laplace_finite
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_laplace_integral_eq_toReal
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ θ : ℝ) (hφ : 0 < φ) (hθ : 0 < θ) (hroot : X.ψ φ = q) :
    X.ψ (φ + θ) - q =
      θ * (X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
        X.σ ^ 2 * φ +
        (∫ z in Ioi (0 : ℝ),
          (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)
          ∂(X.ν.map (fun y : ℝ => -y)))) +
      (X.σ ^ 2 / 2) * θ ^ 2 +
      θ ^ 2 * (∫ t : ℝ, Real.exp (-θ * t) *
        (∫⁻ z : ℝ,
          (if 0 < t ∧ t < z then
            ENNReal.ofReal (z - t) *
              ENNReal.ofReal (Real.exp (-φ * z))
           else 0) ∂(X.ν.map (fun y : ℝ => -y))).toReal ∂volume) := by
  let μ : Measure ℝ := X.ν.map (fun y : ℝ => -y)
  have hν : (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) < ⊤ := by
    exact lt_of_le_of_lt
      (lintegral_mono_set (Set.subset_univ _))
      (by simpa only [Measure.restrict_univ] using X.ν_integrable)
  have hsf : SigmaFinite μ :=
    gaussian_negative_jump_pushforward_sigmaFinite X.ν X.ν_Ici hν
  letI : SigmaFinite μ := hsf
  have hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤ :=
    gaussian_levy_square_integrable_neg_pushforward X.ν hν
  let J : ENNReal := ∫⁻ t : ℝ, ∫⁻ z : ℝ,
    (if 0 < t ∧ t < z then
      ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
        ENNReal.ofReal (Real.exp (-φ * z))
     else 0) ∂μ ∂volume
  have hprod : ENNReal.ofReal (θ ^ 2) * J < ⊤ :=
    gaussian_double_tail_esscher_laplace_finite μ φ θ hφ hθ.le hlevy
  have hweight : ENNReal.ofReal (θ ^ 2) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hθ))
  have hfin : J < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right (ne_of_lt hprod) hweight
  have hreal :
      (∫ t : ℝ, Real.exp (-θ * t) *
        (∫⁻ z : ℝ,
          (if 0 < t ∧ t < z then
            ENNReal.ofReal (z - t) *
              ENNReal.ofReal (Real.exp (-φ * z))
           else 0) ∂μ).toReal ∂volume) = J.toReal :=
    gaussian_double_tail_real_laplace_integral_eq_toReal μ φ θ hfin
  have htail : (∫ z in Ioi (0 : ℝ),
      Real.exp (-φ * z) *
        (Real.exp (-θ * z) - 1 + θ * z) ∂μ) =
      θ ^ 2 * (∫ t : ℝ, Real.exp (-θ * t) *
        (∫⁻ z : ℝ,
          (if 0 < t ∧ t < z then
            ENNReal.ofReal (z - t) *
              ENNReal.ofReal (Real.exp (-φ * z))
           else 0) ∂μ).toReal ∂volume) := by
    rw [hreal]
    exact (gaussian_double_tail_laplace_real_bridge
      μ φ θ hφ hθ hlevy).symm
  have hdenom := gaussian_native_esscher_root_volterra_denominator
    X q φ θ hφ hθ.le hroot
  dsimp [μ] at htail
  rw [htail] at hdenom
  exact hdenom
