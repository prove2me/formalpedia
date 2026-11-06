-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_natural_cash_saturates_any_later_closed_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:18:13.243762+00:00
-- url     : https://prove2.me/submissions/d03defd0-2244-43da-afeb-afbfe467c964

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_stopped_paymentTimes_subset_closed_nat_clock

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ) (T : ℝ)
    (hTn : (n : ℝ) ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) =
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Set.Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) := by
  have hWindow (ω : Ω) :
      paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Set.Iic T =
      paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) := by
    apply Set.inter_eq_left.mpr
    intro t ht
    have hn : t ≤ (n : ℝ) := by
      simpa only [Set.mem_Iic] using
        (avram_limit2_stopped_paymentTimes_subset_closed_nat_clock (ruinTime X x D ω) n ht)
    change t ≤ T
    exact hn.trans hTn
  have hCash (ω : Ω) :
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Set.Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
    rw [hWindow ω]
  simp_rw [hCash]
