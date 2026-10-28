-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_compensated_increment_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:48:34.153856+00:00
-- url     : https://prove2.me/submissions/f1f89cce-31c4-4f81-9e69-1d7e659895d5

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_compensated_increment_mean_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- The compensated exponential of a post-stopping Lévy increment is integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ)) P := by
  have hv := levy_bounded_stopping_compensated_increment_mean_one
    X τ hτ T hbounded h θ hθ
  apply Integrable.of_integral_ne_zero
  rw [hv]
  exact one_ne_zero
