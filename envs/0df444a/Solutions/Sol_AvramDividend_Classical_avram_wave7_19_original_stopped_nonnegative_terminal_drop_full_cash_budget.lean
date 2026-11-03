-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_stopped_nonnegative_terminal_drop_full_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:16:31.611753+00:00
-- url     : https://prove2.me/submissions/ea704d95-ea22-4995-aa1b-bcb122fac265

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_positive_cutoffs_full_expected_cash_bridge
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Drop a source stopped nonnegative terminal value before the original full-cash monotone limit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ) (hT : 0 ≤ T)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (hn : ENNReal.ofReal T < (n : ℝ≥0∞))
    (Terminal : ℕ → Ω → ℝ≥0∞) (budget : ℝ≥0∞)
    (hStopped : ∀ k : ℕ,
      (∫⁻ ω, (((∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / ((k : ℝ) + 1)) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) +
        Terminal k ω) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤
      budget := by
  let A (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
    (∫⁻ t in ({0} : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
      Icc (1 / ((k : ℝ) + 1)) T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
  have hCash (k : ℕ) : (∫⁻ ω, A k ω ∂P) ≤ budget := by
    calc
      (∫⁻ ω, A k ω ∂P) ≤
          (∫⁻ ω, A k ω + Terminal k ω ∂P) := by
        apply lintegral_mono
        intro ω
        calc
          A k ω = A k ω + 0 := (add_zero _).symm
          _ ≤ A k ω + Terminal k ω :=
            add_le_add_right (bot_le : (0 : ℝ≥0∞) ≤ Terminal k ω) _
      _ ≤ budget := hStopped k
  apply avram_wave7_19_original_positive_cutoffs_full_expected_cash_bridge
    X q x T hT D hD n hn budget
  exact hCash
