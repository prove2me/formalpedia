-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_positive_cutoffs_full_expected_cash_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:57:49.320506+00:00
-- url     : https://prove2.me/submissions/a49f6810-4cdb-4a1c-88b2-6f125ff19c18

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_clipped_clock_lower_cutoff_expectation_budget_mct
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_clipped_clock_zero_atom_positive_cutoff_cash_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ) (hT : 0 ≤ T)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (hn : ENNReal.ofReal T < (n : ℝ≥0∞))
    (budget : ℝ≥0∞)
    (hBound : ∀ k : ℕ,
      (∫⁻ ω, ((∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / ((k : ℝ) + 1)) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  apply avram_wave7_19_original_clipped_clock_lower_cutoff_expectation_budget_mct
    X q x T hT D n hn budget
  · intro k
    exact avram_wave7_19_original_clipped_clock_zero_atom_positive_cutoff_cash_measurable
      X q x T D hD n k
  · exact hBound
