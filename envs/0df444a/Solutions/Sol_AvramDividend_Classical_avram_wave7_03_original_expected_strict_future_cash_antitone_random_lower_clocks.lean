-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_expected_strict_future_cash_antitone_random_lower_clocks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:04:07.641854+00:00
-- url     : https://prove2.me/submissions/daa5d3f3-400b-4584-98dd-47acd82563bd

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The exact expected original strictly future Stieltjes dividend cash
    decreases when any path-dependent lower time clock increases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (S T : Ω → ℝ)
    (hST : ∀ ω, S ω ≤ T ω) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (T ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi (S ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by
  apply lintegral_mono
  intro ω
  apply lintegral_mono_set
  intro t ht
  exact ⟨ht.1, lt_of_le_of_lt (hST ω) ht.2⟩
