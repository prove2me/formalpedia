-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_true_stopped_discount_integrableOn_dividendMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:31:44.923768+00:00
-- url     : https://prove2.me/submissions/83ac9f9e-ec2c-48dd-a75d-6fb931d1bf89

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual discounted kernel is real-integrable against source stopped dividend mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) :
    IntegrableOn (fun u : ℝ => Real.exp (-(q * u)))
      (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω) := by
  let μ : Measure ℝ := dividendMeasure D ω
  let s : Set ℝ := paymentTimes σ ∩ Iic (T : ℝ)
  have hs : MeasurableSet s := (paymentTimes_measurable σ).inter measurableSet_Iic
  have hsubset : s ⊆ Icc (0 : ℝ) (T : ℝ) := by
    intro u hu
    exact ⟨(paymentTimes_membership_to_nNReal_active σ u hu.1).1, hu.2⟩
  have hmass : μ s < ⊤ := by
    calc
      μ s ≤ μ (Icc (0 : ℝ) (T : ℝ)) := measure_mono hsubset
      _ = ENNReal.ofReal (rightLimit D T ω) :=
        avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω T
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hcontinuous : Continuous (fun u : ℝ => Real.exp (-(q * u))) := by fun_prop
  have hmeas : AEStronglyMeasurable (fun u : ℝ => Real.exp (-(q * u)))
      (μ.restrict s) := hcontinuous.measurable.aestronglyMeasurable
  have hbound : ∀ᵐ u ∂μ.restrict s,
      ‖Real.exp (-(q * u))‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem hs] with u hu
    have hu0 : 0 ≤ u :=
      (paymentTimes_membership_to_nNReal_active σ u hu.1).1
    have hreal : Real.exp (-(q * u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hq hu0])
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le] using hreal
  exact IntegrableOn.of_bound hmass hmeas 1 hbound
