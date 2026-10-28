-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bounded_stop_future_increment_lintegral_factor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T23:38:21.396114+00:00
-- url     : https://prove2.me/submissions/5b806e6b-5efc-4ef6-b60b-c1eb6df7d09a

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Theorems.Thm_AvramDividend_Classical_esscher_bounded_stop_future_increment_map_law
import Theorems.Thm_AvramDividend_Classical_levy_boundedStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (τ : Ω → ℝ≥0)
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (u T : ℝ≥0) (hT : H + 1 + u ≤ T)
    (A : Set Ω)
    (hA : ∀ s : ℝ≥0,
      MeasurableSet[𝓕 s] (A ∩ {ω : Ω | τ ω ≤ s}))
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ ω in A,
      g (X.X (τ ω + u) ω - X.X (τ ω) ω) ∂
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ))))) =
    (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) A *
      (∫⁻ ω, g (X.X u ω) ∂
        (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ))))) := by
  have hXu : Measurable (X.X u) := (X.adapted u).mono (𝓕.le u) le_rfl
  have hY : Measurable (fun ω => X.X (τ ω + u) ω - X.X (τ ω) ω) :=
    (measurable_pi_apply u).comp
      (levy_boundedStopping_stoppedFuturePath_measurable X τ hstop H hbound)
  have hlaw := esscher_bounded_stop_future_increment_map_law X θ hθ τ hstop H hbound u T hT A hA
  have h1 := lintegral_map hg hY (μ := (P.withDensity (fun ω : Ω => ENNReal.ofReal
          (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))).restrict A)
  rw [← h1]
  simp only at hlaw
  rw [hlaw, lintegral_smul_measure, lintegral_map hg hXu, smul_eq_mul]
