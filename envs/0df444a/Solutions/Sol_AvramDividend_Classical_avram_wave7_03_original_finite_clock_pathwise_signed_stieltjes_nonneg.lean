-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_finite_clock_pathwise_signed_stieltjes_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:03:10.847655+00:00
-- url     : https://prove2.me/submissions/9f75ad66-473e-4eb4-adcd-430650d61a27

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Nonnegativity of the genuine signed real discounted Stieltjes
    payout at every finite original-process stopping clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (τ : ℝ≥0) (q : ℝ) :
    0 ≤ (∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)) := by
  apply integral_nonneg
  intro t
  exact (Real.exp_pos (-(q * t))).le
