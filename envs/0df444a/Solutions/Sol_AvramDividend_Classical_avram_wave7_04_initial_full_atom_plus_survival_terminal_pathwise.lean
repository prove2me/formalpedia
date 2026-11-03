-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_04_initial_full_atom_plus_survival_terminal_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:37:24.150216+00:00
-- url     : https://prove2.me/submissions/50b71408-0316-4577-9989-31fdb60ecc21

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
import Theorems.Thm_AvramDividend_Classical_truncated_dividend_payoff_at_zero_eq_initial_atom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (hpost : ∀ ω, 0 ≤ w (x - rightLimit D 0 ω))
    (ω : Ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
    (if (0 : ℝ≥0∞) < ruinTime X x D ω then
       max 0 (w (x - rightLimit D 0 ω))
     else 0) ≤ w x := by
  classical
  have hInit :=
    avram_wave7_02_original_initial_postpayment_HJB_value_and_full_stieltjes_singleton
      X x D hD w hjump ω
  have hD0 : D 0 ω = 0 := hD.1 ω
  have hCash :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal =
        rightLimit D 0 ω := by
    rw [truncated_dividend_payoff_at_zero_eq_initial_atom
        D hD q (ruinTime X x D ω) ω]
    simp [hD0, ENNReal.toReal_ofReal hInit.2.2]
  rw [hCash]
  by_cases hLive : (0 : ℝ≥0∞) < ruinTime X x D ω
  · simp only [if_pos hLive, max_eq_right (hpost ω)]
    linarith [hInit.1]
  · simp only [if_neg hLive, add_zero]
    linarith [hInit.1, hpost ω]
