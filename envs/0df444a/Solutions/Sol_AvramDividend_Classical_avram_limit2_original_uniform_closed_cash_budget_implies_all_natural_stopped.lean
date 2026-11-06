-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_uniform_closed_cash_budget_implies_all_natural_stopped
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T17:48:07.859384+00:00
-- url     : https://prove2.me/submissions/766b9abb-148e-4d5c-827f-ba53b6ae36e5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_original_real_stopped_cash_le_closed_horizon_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (B : ℝ≥0∞)
    (hClosed : ∀ (T : ℝ) (hT : 0 ≤ T),
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Set.Iic T,
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B) :
    ∀ n : ℕ,
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω) ∂P) ≤ B := by
  intro n
  have hn : (0 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hCast : ENNReal.ofReal (n : ℝ) = (n : ℝ≥0∞) := by
    simp
  have hBound :=
    (avram_limit2_original_real_stopped_cash_le_closed_horizon_cash
      X q x D (n : ℝ) hn).trans (hClosed (n : ℝ) hn)
  simpa only [hCast] using hBound
