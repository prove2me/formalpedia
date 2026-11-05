-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_ruin_by_horizon_closed_cash_eq_strict_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:37:07.02155+00:00
-- url     : https://prove2.me/submissions/37e29acc-8c24-4fea-9b00-6eb76f2d9ed0

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_11_no_terminal_payment_if_clock_ended
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- By original ruin, closed-horizon Cash contains no right-horizon atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (q T : ℝ)
    (hT : 0 < T)
    (hruin_le : ruinTime X x D ω ≤ ENNReal.ofReal T) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  have hNo := avram_wave7_11_no_terminal_payment_if_clock_ended
    (ruinTime X x D ω) T hT hruin_le
  have hSet : paymentTimes (ruinTime X x D ω) ∩ Iic T =
      paymentTimes (ruinTime X x D ω) ∩ Iio T := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Iio]
    constructor
    · rintro ⟨hp, ht⟩
      rcases lt_or_eq_of_le ht with hlt | heq
      · exact ⟨hp, hlt⟩
      · have hs : t ∈ paymentTimes (ruinTime X x D ω) ∩ {T} := by
          exact ⟨hp, by simpa [heq]⟩
        rw [hNo] at hs
        exact hs.elim
    · rintro ⟨hp, ht⟩
      exact ⟨hp, le_of_lt ht⟩
  rw [hSet]
