-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_nat_stopped_cash_exact_zero_or_positive_strict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T18:13:07.786007+00:00
-- url     : https://prove2.me/submissions/7c86ab09-014d-43da-8302-abfb1680049d

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_zero_clock_cash_eq_initial_atom
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_strict_horizon_cash_eq_natural_ruin_stop
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) :
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) =
      if n = 0 then
        (∫⁻ ω, ∫⁻ t in ({0} : Set ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P)
      else
        (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iio (n : ℝ),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P) := by
  intro n
  by_cases hn : n = 0
  · subst n
    simpa using
      (avram_limit2_original_zero_clock_cash_eq_initial_atom X q x D)
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hT : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast hnpos
    have hCast : ENNReal.ofReal (n : ℝ) = (n : ℝ≥0∞) := by simp
    have h := avram_limit2_original_strict_horizon_cash_eq_natural_ruin_stop
      X q x D (n : ℝ) hT
    simpa only [if_neg hn, hCast] using h
