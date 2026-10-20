-- Prove2me | solution 1 for AvramDividend.Classical.zero_cap_admissible_dividendValue_le_barrier_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T15:35:52.801799+00:00
-- url     : https://prove2.me/submissions/7bfcf907-5029-4226-84e8-aabd1a2ec3d9

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_zero_cap_dividend_payoff_zero_at_immediate_ruin
import Theorems.Thm_AvramDividend_Classical_zero_cap_dividendMeasure_restrict_paymentTimes_eq_of_pos_ruin
import Theorems.Thm_AvramDividend_Classical_zero_cap_ruinTime_le_barrier_ruinTime
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-! Exact parent target 570b5248-37cd-45e1-a600-cb46bf273fae.
Source only. Do NOT submit while any prerequisite child is still Open. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X 0 0 D) :
    dividendValue X q 0 D ≤
      dividendValue X q 0 (barrierStrategy X 0 0) := by
  let B : ℝ≥0 → Ω → ℝ := barrierStrategy X 0 0
  unfold dividendValue
  apply lintegral_mono
  intro ω
  let σ := ruinTime X 0 D ω
  let τ := ruinTime X 0 B ω
  have horder : σ ≤ τ :=
    zero_cap_ruinTime_le_barrier_ruinTime X D hD ω
  have hpay_subset : paymentTimes σ ⊆ paymentTimes τ := by
    intro t ht
    rcases ht with ⟨ht0, hzero | hlt⟩
    · exact ⟨ht0, Or.inl hzero⟩
    · exact ⟨ht0, Or.inr (lt_of_lt_of_le hlt horder)⟩
  change
    (∫⁻ t in paymentTimes σ,
       ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    (∫⁻ t in paymentTimes τ,
       ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure B ω))
  by_cases hσ0 : σ = 0
  · have hvanish :
        (∫⁻ t in paymentTimes σ,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) = 0 :=
      zero_cap_dividend_payoff_zero_at_immediate_ruin X q D hD ω hσ0
    rw [hvanish]
    exact zero_le
  · have hσpos : 0 < σ :=
      lt_of_le_of_ne (show (0 : ℝ≥0∞) ≤ σ from zero_le) (Ne.symm hσ0)
    have hmeas :
        (dividendMeasure D ω).restrict (paymentTimes σ) =
        (dividendMeasure B ω).restrict (paymentTimes σ) :=
      zero_cap_dividendMeasure_restrict_paymentTimes_eq_of_pos_ruin
        X D hD ω hσpos
    have hintegral :
        (∫⁻ t in paymentTimes σ,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
        (∫⁻ t in paymentTimes σ,
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure B ω)) := by
      change
        (∫⁻ t, ENNReal.ofReal (Real.exp (-(q * t))) ∂
          ((dividendMeasure D ω).restrict (paymentTimes σ))) =
        (∫⁻ t, ENNReal.ofReal (Real.exp (-(q * t))) ∂
          ((dividendMeasure B ω).restrict (paymentTimes σ)))
      rw [hmeas]
    exact hintegral.le.trans (lintegral_mono_set hpay_subset)
