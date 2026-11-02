-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_expected_preruin_complete_stieltjes_budget_monotone_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:49:47.402702+00:00
-- url     : https://prove2.me/submissions/cb1153a8-eab4-489c-a8e2-b324e0fe47b9

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_expected_preruin_complete_stieltjes_localisation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ≥0) (q : ℝ) (w : ℝ → ℝ)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτmeas : ∀ n, Measurable (τ n))
    (hτmono : ∀ ω, Monotone (fun n => τ n ω))
    (hτsup : ∀ ω, (⨆ n, τ n ω) = ruinTime X x D ω)
    (hBudget : ∀ n,
      (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (τ n ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω ∂P) ≤
        ENNReal.ofReal (w x)) :
    (∫⁻ ω : Ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω ∂P) ≤
      ENNReal.ofReal (w x) := by
  rw [avram_wave4_04b_expected_preruin_complete_stieltjes_localisation
    X x D hD T q τ hτmeas hτmono hτsup]
  exact iSup_le hBudget
