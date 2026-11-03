-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_spatial_localisation_vanishing_jump_error_cash_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:06:05.203336+00:00
-- url     : https://prove2.me/submissions/3c70bece-550d-4b14-9314-5e63a0c23fd6

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_spatial_localisation_ae_exhaustion_cash_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Original-source spatial boundary passage with an arbitrarily vanishing jump-truncation error. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (LocalCash : ℕ → Ω → ℝ≥0∞)
    (hLocalMeas : ∀ k : ℕ, Measurable (LocalCash k))
    (hLocalMon : ∀ ω : Ω, Monotone (fun k : ℕ => LocalCash k ω))
    (hExhaust : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
        ⨆ k : ℕ, LocalCash k ω)
    (budget : ℝ≥0∞)
    (hApprox : ∀ (k : ℕ) (ε : NNReal), 0 < ε → budget < ⊤ →
      (∫⁻ ω, LocalCash k ω ∂P) ≤ budget + ENNReal.ofNNReal ε) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤
      budget := by
  apply avram_wave7_19_original_spatial_localisation_ae_exhaustion_cash_budget
    X q x T D hD LocalCash hLocalMeas hLocalMon hExhaust budget
  intro k
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hbudget
  exact hApprox k ε hε hbudget
