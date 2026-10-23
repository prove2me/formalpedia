-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_native_esscher_root_volterra_denominator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T14:46:40.262272+00:00
-- url     : https://prove2.me/submissions/71402f1a-600a-4ce2-8b84-3e41694f0a74

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_gaussian_levy_square_integrable_neg_pushforward
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_psi_volterra_denominator_of_root
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Derive the Gaussian Volterra denominator directly from the native Lévy triplet. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ θ : ℝ) (hφ : 0 < φ) (hθ : 0 ≤ θ) (hroot : X.ψ φ = q) :
    X.ψ (φ + θ) - q =
      θ * (X.c - (X.ν.map (fun y : ℝ => -y)).real ({1} : Set ℝ) +
        X.σ ^ 2 * φ +
        (∫ z in Ioi (0 : ℝ),
          (if z ≤ 1 then z else 0) - z * Real.exp (-φ * z)
          ∂(X.ν.map (fun y : ℝ => -y)))) +
      (X.σ ^ 2 / 2) * θ ^ 2 +
      (∫ z in Ioi (0 : ℝ),
        Real.exp (-φ * z) *
          (Real.exp (-θ * z) - 1 + θ * z)
        ∂(X.ν.map (fun y : ℝ => -y))) := by
  have hneg :
      (∫⁻ y in Iio (0 : ℝ),
        ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) < ⊤ := by
    exact lt_of_le_of_lt
      (lintegral_mono_set (Set.subset_univ _))
      (by simpa only [Measure.restrict_univ] using X.ν_integrable)
  have hpush := gaussian_levy_square_integrable_neg_pushforward X.ν hneg
  exact gaussian_esscher_psi_volterra_denominator_of_root
    X q φ θ hφ hθ hroot hpush
