-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_zero_cap_underbudget_violation_occurs_after_zero_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:00:43.578234+00:00
-- url     : https://prove2.me/submissions/a0e5fe50-3333-4ebd-b5c0-951530ca2caf

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_zero_cap_any_underbudget_has_positive_finite_horizon_excess
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_original_admissible_zero_start_zero_horizon_expected_cash_eq_zero
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Any subthreshold original reflected BV dividend allowance is violated
at a finite horizon strictly later than T=0; the original initial
Stieltjes atom is zero at zero reserve. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) (W : ℝ)
    (hUnder : W < X.drift / (q + (X.ν (Iio (0 : ℝ))).toReal)) :
    ∃ n : ℕ, 0 < n ∧ ENNReal.ofReal W <
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) := by
  obtain ⟨n, hn⟩ :=
    avram_wave7_09_bv_zero_cap_any_underbudget_has_positive_finite_horizon_excess
      X hX hBV hFinite q hq W hUnder
  have hD : IsAdmissibleLe X 0 (0 : ℝ≥0∞) (barrierStrategy X 0 0) := by
    simpa only [ENNReal.ofReal_zero] using
      (barrierStrategy_admissibleLe_nonnegative_barrier
        X 0 0 (le_refl (0 : ℝ)) (le_refl (0 : ℝ)))
  refine ⟨n, ?_, hn⟩
  by_contra hNo
  have hn0 : n = 0 := by omega
  subst n
  have hZero :=
    avram_wave7_09_original_admissible_zero_start_zero_horizon_expected_cash_eq_zero
      X (0 : ℝ≥0∞) (barrierStrategy X 0 0) hD q
  have hAtZero : ENNReal.ofReal W <
      (∫⁻ ω, ∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) := by
    simpa only [Nat.cast_zero] using hn
  rw [hZero] at hAtZero
  exact (not_lt_of_ge (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal W)) hAtZero
