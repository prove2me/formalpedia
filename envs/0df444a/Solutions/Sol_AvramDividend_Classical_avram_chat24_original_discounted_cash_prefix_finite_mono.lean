-- Prove2me | solution 1 for AvramDividend.Classical.avram_chat24_original_discounted_cash_prefix_finite_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:12:42.918312+00:00
-- url     : https://prove2.me/submissions/2eaf4d71-acbf-4865-91c3-2a968b94faff

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Discounted original dividend payments grow with the genuine strict clock prefix. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (s T : ℝ) (hT : 0 ≤ T) (hs : s ≤ T) :
    (∫⁻ t in paymentTimes σ ∩ Iio s,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal ≤
    (∫⁻ t in paymentTimes σ ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal := by
  have hfinClosed :=
    avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
      D hD ω σ ⟨T, hT⟩ q hq
  have hInclClosed : paymentTimes σ ∩ Iio T ⊆
      paymentTimes σ ∩ Iic (T : ℝ) := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    change t ≤ T
    exact le_of_lt ht.2
  have hfinOpen : (∫⁻ t in paymentTimes σ ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hInclClosed) hfinClosed
  have hIncl : paymentTimes σ ∩ Iio s ⊆
      paymentTimes σ ∩ Iio T := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    change t < T
    exact lt_of_lt_of_le ht.2 hs
  exact ENNReal.toReal_mono (ne_of_lt hfinOpen)
    (lintegral_mono_set hIncl)
