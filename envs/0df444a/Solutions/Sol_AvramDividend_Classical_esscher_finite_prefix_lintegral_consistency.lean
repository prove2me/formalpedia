-- Prove2me | solution 1 for AvramDividend.Classical.esscher_finite_prefix_lintegral_consistency
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:21:07.532059+00:00
-- url     : https://prove2.me/submissions/3d0be9ec-e351-4a4e-939c-526a2a0ee984

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Theorems.Thm_AvramDividend_Classical_esscher_path_prefix_trim_measure_consistency
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- All nonnegative measurable functionals of a finite past have
the same expectation under every later Esscher terminal law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s T : ℝ≥0) (hsT : s ≤ T)
    (f : Ω → ℝ≥0∞) (hf : Measurable[𝓕 s] f) :
    (∫⁻ ω, f ω ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
    (∫⁻ ω, f ω ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))) := by
  calc
    (∫⁻ ω, f ω ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
      (∫⁻ ω, f ω ∂
        (@Measure.trim Ω (𝓕 s) mΩ
          (P.withDensity (fun ω : Ω => ENNReal.ofReal
            (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))
          (𝓕.le s))) := by
            exact (lintegral_trim (𝓕.le s) hf).symm
    _ = (∫⁻ ω, f ω ∂
        (@Measure.trim Ω (𝓕 s) mΩ
          (P.withDensity (fun ω : Ω => ENNReal.ofReal
            (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))
          (𝓕.le s))) := by
            rw [esscher_path_prefix_trim_measure_consistency X θ hθ s T hsT]
    _ = (∫⁻ ω, f ω ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ))))) := by
            exact lintegral_trim (𝓕.le s) hf
