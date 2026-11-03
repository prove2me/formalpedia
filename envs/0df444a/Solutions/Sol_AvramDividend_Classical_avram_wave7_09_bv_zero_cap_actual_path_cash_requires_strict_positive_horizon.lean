-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_zero_cap_actual_path_cash_requires_strict_positive_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:52:55.760197+00:00
-- url     : https://prove2.me/submissions/92e1666a-7c0a-4f07-9f0b-82ef8d97a09c

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_finite_activity_zero_cap_actual_path_has_positive_finite_horizon_cash
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_original_admissible_zero_start_zero_horizon_cash_eq_zero
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_admissibleLe_nonnegative_barrier

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The positive original sample cash witness at zero cap is strictly
later than the zero horizon, since no original zero-start admissible
strategy pays a Stieltjes atom by horizon zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ (n : ℕ) (ω : Ω), 0 < n ∧
      0 < (∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω)) := by
  obtain ⟨n, ω, hn⟩ :=
    avram_wave7_09_bv_finite_activity_zero_cap_actual_path_has_positive_finite_horizon_cash
      X hX hBV hFinite q hq
  have hD : IsAdmissibleLe X 0 (0 : ℝ≥0∞) (barrierStrategy X 0 0) := by
    simpa only [ENNReal.ofReal_zero] using
      (barrierStrategy_admissibleLe_nonnegative_barrier
        X 0 0 (le_refl (0 : ℝ)) (le_refl (0 : ℝ)))
  refine ⟨n, ω, ?_, hn⟩
  by_contra hNot
  have hn0 : n = 0 := by omega
  subst n
  have hZero :=
    avram_wave7_09_original_admissible_zero_start_zero_horizon_cash_eq_zero
      X (0 : ℝ≥0∞) (barrierStrategy X 0 0) hD q
      (ruinTime X 0 (barrierStrategy X 0 0) ω) ω
  have hAtZero : 0 <
      (∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω)) := by
    simpa only [Nat.cast_zero] using hn
  rw [hZero] at hAtZero
  exact (lt_irrefl _) hAtZero
