-- Prove2me | solution 1 for AvramDividend.Classical.truncated_zero_horizon_bound_forces_initial_excess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T16:19:30.091989+00:00
-- url     : https://prove2.me/submissions/2181e761-507f-4ef6-85e7-290602209968

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissibleLe_rightLimit_zero_ge_excess
import Theorems.Thm_AvramDividend_Classical_truncated_dividend_payoff_at_zero_eq_initial_atom
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! SOURCE CANDIDATE ONLY. Do not submit before the imported time-zero lemma is Proved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x c : ℝ) (hc : 0 ≤ c) (hcx : c < x)
    (q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hbound :
      (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
          ENNReal.ofReal (w x)) :
    ENNReal.ofReal (x - c) ≤ ENNReal.ofReal (w x) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hlower (ω : Ω) :
      ENNReal.ofReal (x - c) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
    rw [truncated_dividend_payoff_at_zero_eq_initial_atom
      D hD.1.1 q (ruinTime X x D ω) ω]
    have hD0 : D 0 ω = 0 := hD.1.1.1 ω
    rw [hD0, sub_zero]
    exact ENNReal.ofReal_le_ofReal
      (admissibleLe_rightLimit_zero_ge_excess X x c hc hcx D hD ω)
  calc
    ENNReal.ofReal (x - c) =
        (∫⁻ _ : Ω, ENNReal.ofReal (x - c) ∂P) := by simp
    _ ≤ (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (0 : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) :=
      lintegral_mono hlower
    _ ≤ ENNReal.ofReal (w x) := hbound
