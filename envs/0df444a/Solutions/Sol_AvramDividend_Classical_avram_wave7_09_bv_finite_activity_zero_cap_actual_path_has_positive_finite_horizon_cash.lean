-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_09_bv_finite_activity_zero_cap_actual_path_has_positive_finite_horizon_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:35:00.292179+00:00
-- url     : https://prove2.me/submissions/b7aa106c-50b7-4eea-9e51-2e48b50c0949

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_09_bv_finite_activity_zero_cap_zero_start_positive_horizon_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Positive original expected cash forces an actual sample path with
positive complete stopped discounted Stieltjes cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q) :
    ∃ (n : ℕ) (ω : Ω), 0 <
      (∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω)) := by
  obtain ⟨n, hn⟩ :=
    avram_wave7_09_bv_finite_activity_zero_cap_zero_start_positive_horizon_cash
      X hX hBV hFinite q hq
  by_contra hNo
  have hAllZero : ∀ ω : Ω,
      (∫⁻ t in
        paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure (barrierStrategy X 0 0) ω)) = 0 := by
    intro ω
    by_contra hne
    have hp : 0 <
        (∫⁻ t in
          paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure (barrierStrategy X 0 0) ω)) :=
      lt_of_le_of_ne bot_le (Ne.symm hne)
    exact hNo ⟨n, ω, hp⟩
  have hExpectation : (∫⁻ ω, ∫⁻ t in
      paymentTimes (ruinTime X 0 (barrierStrategy X 0 0) ω) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure (barrierStrategy X 0 0) ω) ∂P) = 0 := by
    simp only [hAllZero, lintegral_zero]
  rw [hExpectation] at hn
  exact (lt_irrefl _) hn
