-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_stopped_cash_eventual_exact_equality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:22:14.245202+00:00
-- url     : https://prove2.me/submissions/e8c6d5d8-9e42-4e2d-9852-24cda35ad4b4

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

/-- Eventual equality of exact original payment domains preserves the true random Stieltjes cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ)
    (S : ℕ → Ω → ℝ≥0∞)
    (hDomains : ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic T =
      paymentTimes (ruinTime X x D ω) ∩ Iic T) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∫⁻ t in paymentTimes (min (ruinTime X x D ω) (S n ω)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  filter_upwards [hDomains] with ω hω
  obtain ⟨N, hN⟩ := hω
  refine ⟨N, ?_⟩
  intro n hn
  rw [hN n hn]
