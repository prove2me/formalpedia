-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_stopped_bounded_kernel_cash_le_total_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:20:31.294196+00:00
-- url     : https://prove2.me/submissions/18c35674-c59f-4626-b881-3f74ac1eb505

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

/-- Any bounded nonnegative original payment-time kernel is controlled by full Stieltjes mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (g : ℝ → ℝ≥0∞)
    (hg : ∀ u ∈ paymentTimes σ ∩ Iic (T : ℝ), g u ≤ 1) :
    (∫⁻ u in paymentTimes σ ∩ Iic (T : ℝ), g u ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (rightLimit D T ω) := by
  let μ : Measure ℝ := dividendMeasure D ω
  let s : Set ℝ := paymentTimes σ ∩ Iic (T : ℝ)
  have hs : MeasurableSet s := (paymentTimes_measurable σ).inter measurableSet_Iic
  have hsubset : s ⊆ Icc (0 : ℝ) (T : ℝ) := by
    intro u hu
    exact ⟨(paymentTimes_membership_to_nNReal_active σ u hu.1).1, hu.2⟩
  calc
    (∫⁻ u in s, g u ∂μ) ≤ (∫⁻ u in s, (1 : ℝ≥0∞) ∂μ) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hs] with u hu
      exact hg u hu
    _ = μ s := by simp
    _ ≤ μ (Icc (0 : ℝ) (T : ℝ)) := measure_mono hsubset
    _ = ENNReal.ofReal (rightLimit D T ω) :=
      avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω T
