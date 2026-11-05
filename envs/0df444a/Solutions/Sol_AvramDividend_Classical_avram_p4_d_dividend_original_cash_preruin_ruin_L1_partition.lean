-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_cash_preruin_ruin_L1_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:41:40.516879+00:00
-- url     : https://prove2.me/submissions/8b300622-dde5-4191-b725-f9fd55d4518f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (τ : Ω → ℝ≥0) (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (s : Set Ω)
    (hs : s = {ω | τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω})
    (hsMeas : MeasurableSet s) :
    Integrable (s.indicator Cash) P ∧
    Integrable (sᶜ.indicator Cash) P ∧
    (∀ ω, Cash ω =
      s.indicator Cash ω + sᶜ.indicator Cash ω) := by
  classical
  refine ⟨hCashI.indicator hsMeas,
    hCashI.indicator hsMeas.compl, ?_⟩
  intro ω
  by_cases hω : ω ∈ s
  · have hc : ω ∉ sᶜ := by simpa using hω
    simp only [Set.indicator_of_mem hω,
      Set.indicator_of_notMem hc, add_zero]
  · have hc : ω ∈ sᶜ := by simpa using hω
    simp only [Set.indicator_of_notMem hω,
      Set.indicator_of_mem hc, zero_add]
