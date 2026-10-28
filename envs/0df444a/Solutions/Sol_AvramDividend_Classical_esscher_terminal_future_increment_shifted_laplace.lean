-- Prove2me | solution 1 for AvramDividend.Classical.esscher_terminal_future_increment_shifted_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T16:18:07.984363+00:00
-- url     : https://prove2.me/submissions/90e4e562-aeb7-4eff-98b0-1647828a1642

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_map_law
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_shifted_laplace

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- The Esscher-shifted exponent is the Laplace exponent of each future increment
under any later finite-terminal tilted law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ η : ℝ) (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (s u T : ℝ≥0) (hT : s + u ≤ T) :
    (∫ ω, Real.exp (η * (X.X (s + u) ω - X.X s ω)) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
      Real.exp ((u : ℝ) * (X.ψ (θ + η) - X.ψ θ)) := by
  have hY : Measurable (fun ω : Ω => X.X (s + u) ω - X.X s ω) :=
    ((X.adapted (s + u)).mono (𝓕.le (s + u)) le_rfl).sub
      ((X.adapted s).mono (𝓕.le s) le_rfl)
  have hXu : Measurable (X.X u) :=
    (X.adapted u).mono (𝓕.le u) le_rfl
  have hf : StronglyMeasurable (fun y : ℝ => Real.exp (η * y)) :=
    ((Real.continuous_exp.measurable).comp
      (measurable_const.mul measurable_id)).stronglyMeasurable
  calc
    (∫ ω, Real.exp (η * (X.X (s + u) ω - X.X s ω)) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
      ∫ y : ℝ, Real.exp (η * y) ∂
        Measure.map (fun ω : Ω => X.X (s + u) ω - X.X s ω)
          (P.withDensity (fun ω : Ω => ENNReal.ofReal
            (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) := by
              exact (integral_map_of_stronglyMeasurable hY hf).symm
    _ = ∫ y : ℝ, Real.exp (η * y) ∂
      Measure.map (X.X u)
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))) := by
            rw [esscher_terminal_increment_map_law X θ hθ s u T hT]
    _ = (∫ ω, Real.exp (η * X.X u ω) ∂
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))) := by
          exact integral_map_of_stronglyMeasurable hXu hf
    _ = Real.exp ((u : ℝ) * (X.ψ (θ + η) - X.ψ θ)) :=
      chat04_esscher_weighted_finite_horizon_shifted_laplace X u θ η hθ hη
