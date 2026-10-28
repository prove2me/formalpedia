-- Prove2me | solution 1 for AvramDividend.Classical.esscher_terminal_increment_map_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T15:53:37.435198+00:00
-- url     : https://prove2.me/submissions/f0fcd946-dcd2-42fd-98e5-226f20d278e2

import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_esscher_terminal_increment_cylinder_factorization
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_weighted_finite_horizon_probability
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every increment under the later terminal Esscher law has the tilted one-time law. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (s u T : ℝ≥0) (hT : s + u ≤ T) :
    Measure.map (fun ω : Ω => X.X (s + u) ω - X.X s ω)
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X T ω - (T : ℝ) * X.ψ θ)))) =
    Measure.map (X.X u)
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X u ω - (u : ℝ) * X.ψ θ)))) := by
  haveI : IsProbabilityMeasure
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (θ * X.X s ω - (s : ℝ) * X.ψ θ)))) :=
    chat04_esscher_weighted_finite_horizon_probability X s θ hθ
  have hY : Measurable (fun ω : Ω => X.X (s + u) ω - X.X s ω) :=
    ((X.adapted (s + u)).mono (𝓕.le (s + u)) le_rfl).sub
      ((X.adapted s).mono (𝓕.le s) le_rfl)
  have hXu : Measurable (X.X u) :=
    (X.adapted u).mono (𝓕.le u) le_rfl
  ext B hB
  rw [Measure.map_apply hY hB, Measure.map_apply hXu hB]
  have h :=
    esscher_terminal_increment_cylinder_factorization
      X θ hθ s u T hT Set.univ
      (by exact MeasurableSet.univ) B hB
  simpa only [Set.univ_inter, measure_univ, one_mul] using h
