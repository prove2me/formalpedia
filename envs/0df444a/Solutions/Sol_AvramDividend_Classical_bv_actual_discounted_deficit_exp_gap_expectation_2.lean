-- Prove2me | solution 2 for AvramDividend.Classical.bv_actual_discounted_deficit_exp_gap_expectation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T00:22:41.793869+00:00
-- url     : https://prove2.me/submissions/e1c3660c-bf43-43ce-a05d-27353e4b87f8

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_normalised_laplace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (t : ℝ≥0) (θ : ℝ) (hθ : 1 ≤ θ) :
    (∫ ω, (1 : ℝ) -
        Real.exp (θ * X.X t ω) *
          Real.exp (-((t : ℝ) * X.drift * θ)) ∂P) =
      1 - Real.exp (-((t : ℝ) *
        ∫ y in Iio (0 : ℝ), (1 - Real.exp (θ * y)) ∂X.ν)) := by
  haveI := X.isProbability
  have h := bv_actual_levy_drift_normalised_laplace X hBV t θ hθ
  have hi : Integrable (fun ω => Real.exp (θ * X.X t ω) * Real.exp (-((t : ℝ) * X.drift * θ))) P :=
    Integrable.of_integral_ne_zero (by rw [h]; exact (Real.exp_pos _).ne')
  rw [integral_sub (integrable_const 1) hi, h]
  simp
