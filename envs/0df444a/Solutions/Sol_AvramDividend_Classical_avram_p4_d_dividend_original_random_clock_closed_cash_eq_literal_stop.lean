-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_closed_cash_eq_literal_stop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:48:36.688197+00:00
-- url     : https://prove2.me/submissions/a9388b5a-68ca-40df-9400-f4250cbdd757

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The exact original finite-window Stieltjes identity holds pathwise at any random clock, in particular the true stopped clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (τ : Ω → ℝ≥0) :
    ∀ ω : Ω,
      (∫⁻ s : ℝ, (if s ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * s))) else 0)
        ∂((dividendMeasure D ω).restrict (Icc (0 : ℝ) (τ ω : ℝ)))) =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by
  intro ω
  exact avram_p4_d_dividend_original_closed_restrict_cash_eq_literal_stop
    X x D hD q ω (τ ω)
