-- Prove2me | solution 1 for AvramDividend.Classical.levy_bounded_stopping_increment_exp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:48:29.553804+00:00
-- url     : https://prove2.me/submissions/99955d47-d33d-4f8f-bc0d-27fff3889f4e

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_bounded_stopping_increment_laplace
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal

/-- Exponential moments after bounded Lévy stopping times are genuinely Bochner integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * (X.X (τ ω + h) ω - X.X (τ ω) ω))) P := by
  have hv := levy_bounded_stopping_increment_laplace X τ hτ T hbounded h θ hθ
  apply Integrable.of_integral_ne_zero
  rw [hv]
  exact Real.exp_ne_zero _
