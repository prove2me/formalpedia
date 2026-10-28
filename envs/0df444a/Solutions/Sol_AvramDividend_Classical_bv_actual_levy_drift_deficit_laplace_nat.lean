-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_levy_drift_deficit_laplace_nat
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:43:36.872445+00:00
-- url     : https://prove2.me/submissions/2c19dc66-3208-43c7-a282-047cbbc23899

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_normalised_laplace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual bounded-variation drift deficit has the integer Laplace transform. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (t : ℝ≥0) (n : ℕ) (hn : 1 ≤ n) :
    (∫ ω, Real.exp ((n : ℝ) * (-((t : ℝ) * X.drift - X.X t ω))) ∂P) =
      Real.exp (-((t : ℝ) *
        ∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂X.ν)) := by
  have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  calc
    (∫ ω, Real.exp ((n : ℝ) * (-((t : ℝ) * X.drift - X.X t ω))) ∂P) =
        (∫ ω, Real.exp ((n : ℝ) * X.X t ω) *
            Real.exp (-((t : ℝ) * X.drift * (n : ℝ))) ∂P) := by
          apply integral_congr_ae
          filter_upwards with ω
          rw [← Real.exp_add]
          congr 1
          ring
    _ = Real.exp (-((t : ℝ) *
        ∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂X.ν)) :=
      bv_actual_levy_drift_normalised_laplace X hBV t (n : ℝ) hnReal
