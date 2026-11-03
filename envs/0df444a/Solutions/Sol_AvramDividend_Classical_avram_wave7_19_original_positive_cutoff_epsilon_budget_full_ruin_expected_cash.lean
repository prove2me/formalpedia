-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_positive_cutoff_epsilon_budget_full_ruin_expected_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:01:29.478379+00:00
-- url     : https://prove2.me/submissions/0e1f553d-ddac-4ccc-9e77-db142a3b3f96

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_positive_cutoffs_full_expected_cash_bridge
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
    (hApprox : ∀ k : ℕ, ∀ ε : NNReal, 0 < ε → budget < ⊤ →
      (∫⁻ ω, ((∫⁻ t in ({0} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩
        Icc (1 / ((k : ℝ) + 1)) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) ∂P) ≤
        budget + ENNReal.ofNNReal ε) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  apply avram_wave7_19_original_positive_cutoffs_full_expected_cash_bridge
    X q x T hT D hD n hn budget
  intro k
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hbudget
  exact hApprox k ε hε hbudget
