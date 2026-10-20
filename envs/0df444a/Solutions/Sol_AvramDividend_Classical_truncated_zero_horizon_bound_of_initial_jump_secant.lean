-- Prove2me | solution 1 for AvramDividend.Classical.truncated_zero_horizon_bound_of_initial_jump_secant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T19:53:46.245821+00:00
-- url     : https://prove2.me/submissions/d9dc40b6-f733-4079-8060-67df248f8d9b

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_truncated_dividend_payoff_at_zero_eq_initial_atom
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hjump : ∀ ω,
       rightLimit D 0 ω - D 0 ω ≤
         w x - w (x - (rightLimit D 0 ω - D 0 ω)))
    (hpost : ∀ ω, 0 ≤ w (x - (rightLimit D 0 ω - D 0 ω))) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (w x) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hpath (ω : Ω) :
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (w x) := by
    rw [truncated_dividend_payoff_at_zero_eq_initial_atom
      D hD q (ruinTime X x D ω) ω]
    apply ENNReal.ofReal_le_ofReal
    have hj := hjump ω
    have hp := hpost ω
    linarith
  calc
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
        (∫⁻ _ : Ω, ENNReal.ofReal (w x) ∂P) :=
      lintegral_mono hpath
    _ = ENNReal.ofReal (w x) := by simp
