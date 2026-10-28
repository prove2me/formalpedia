-- Prove2me | solution 2 for AvramDividend.Classical.bv_infinite_activity_deficit_positive_grid
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:23:37.255452+00:00
-- url     : https://prove2.me/submissions/79f1ea76-311a-47a8-9e5d-f7baef570678

import Theorems.Thm_AvramDividend_Classical_bv_infinite_activity_drift_deficit_zero_atom
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hνinf : X.ν (Iio (0 : ℝ)) = ⊤)
    (grid : ℕ → ℝ≥0) (hgrid : ∀ n, 0 < grid n) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      0 < X.drift * (grid n : ℝ) - X.X (grid n) ω := by
  have := X.isProbability
  rw [ae_all_iff]
  intro n
  have h1 := AvramDividend.Classical.bv_actual_levy_drift_upper_ae_fixed_time X hBV (grid n)
  have h2 := AvramDividend.Classical.bv_infinite_activity_drift_deficit_zero_atom X hBV hνinf
    (grid n) (hgrid n)
  have h3 : P {ω : Ω | ((grid n : ℝ≥0) : ℝ) * X.drift - X.X (grid n) ω = 0} = 0 :=
    (measureReal_eq_zero_iff).1 h2
  have h4 : ∀ᵐ ω ∂P, ω ∉ {ω : Ω | ((grid n : ℝ≥0) : ℝ) * X.drift - X.X (grid n) ω = 0} :=
    measure_eq_zero_iff_ae_notMem.1 h3
  filter_upwards [h1, h4] with ω hω hω'
  rcases lt_or_eq_of_le hω with h | h
  · linarith
  · exact absurd (show ((grid n : ℝ≥0) : ℝ) * X.drift - X.X (grid n) ω = 0 by linarith) hω'
