-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_stopped_dominated_mass_le_discounted_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:28:48.475902+00:00
-- url     : https://prove2.me/submissions/5712f56d-aa06-4c0b-957b-cf4e442e6d26

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Every path-dependent submeasure of the original dividend measure has
stopped mass controlled by the *actual* discounted stopped cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (ν : Measure ℝ) (hdom : ν ≤ dividendMeasure D ω)
    (q : ℝ) (hq : 0 ≤ q) :
    ENNReal.ofReal (Real.exp (-(q * (T : ℝ)))) *
      ν (paymentTimes σ ∩ Iic (T : ℝ)) ≤
      ∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω) := by
  let S : Set ℝ := paymentTimes σ ∩ Iic (T : ℝ)
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(q * (T : ℝ))))
  have hS : MeasurableSet S :=
    (paymentTimes_measurable σ).inter measurableSet_Iic
  have hmem : ∀ᵐ s ∂(dividendMeasure D ω).restrict S, s ∈ S :=
    ae_restrict_mem hS
  have hdiscount : ∀ᵐ s ∂(dividendMeasure D ω).restrict S,
      c ≤ ENNReal.ofReal (Real.exp (-(q * s))) := by
    filter_upwards [hmem] with s hs
    have hqt : q * s ≤ q * (T : ℝ) :=
      mul_le_mul_of_nonneg_left hs.2 hq
    have he : Real.exp (-(q * (T : ℝ))) ≤ Real.exp (-(q * s)) :=
      Real.exp_le_exp.mpr (neg_le_neg hqt)
    exact ENNReal.ofReal_le_ofReal he
  change c * ν S ≤ ∫⁻ s in S,
    ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
  calc
    c * ν S ≤ c * (dividendMeasure D ω) S := by
      gcongr <;> exact hdom S
    _ = ∫⁻ s in S, c ∂(dividendMeasure D ω) :=
      (setLIntegral_const S c).symm
    _ ≤ ∫⁻ s in S, ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω) := lintegral_mono_ae hdiscount
