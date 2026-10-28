-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_small_positive_deficit_probability_explicit_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T14:25:01.516969+00:00
-- url     : https://prove2.me/submissions/2764c30f-d9c4-4b31-8089-5a701722dd3b

import Theorems.Thm_AvramDividend_Classical_nonnegative_deficit_laplace_integrability_package
import Theorems.Thm_AvramDividend_Classical_bv_actual_small_positive_deficit_probability_le_exp_laplace_gap
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Actual BV Lévy deficit measurability and nonnegativity discharge all Laplace-gap side conditions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) (n : ℕ) (hn : 1 ≤ n) (a : ℝ) :
    P.real {ω : Ω |
      0 < (t : ℝ) * X.drift - X.X t ω ∧
      (n : ℝ) * ((t : ℝ) * X.drift - X.X t ω) ≤ a} ≤
    Real.exp a *
      (Real.exp (-((t : ℝ) *
        ∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂X.ν)) -
        Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal))) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let D : Ω → ℝ := fun ω => (t : ℝ) * X.drift - X.X t ω
  have hMeas : Measurable D :=
    measurable_const.sub (X.adapted.measurable)
  have hNonneg : ∀ᵐ ω ∂P, 0 ≤ D ω := by
    filter_upwards [bv_actual_levy_drift_upper_ae_fixed_time X hBV t] with ω hUpper
    dsimp [D]
    linarith
  obtain ⟨hSmall, hZero, hLeft, hRight, hZeroInt⟩ :=
    nonnegative_deficit_laplace_integrability_package
      P D hMeas hNonneg (n : ℝ) a (Nat.cast_nonneg n)
  simpa only [D] using
    (bv_actual_small_positive_deficit_probability_le_exp_laplace_gap
      X hBV hFinite t n hn a D rfl
      hSmall hZero hLeft hRight hZeroInt)
