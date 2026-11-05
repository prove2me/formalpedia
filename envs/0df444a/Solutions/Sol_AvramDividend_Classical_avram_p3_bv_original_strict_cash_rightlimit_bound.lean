-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_bv_original_strict_cash_rightlimit_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T09:12:37.505445+00:00
-- url     : https://prove2.me/submissions/ba752bed-70fe-4865-9618-ee7f958c5dbc

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

/-- Genuine original discounted Stieltjes cash strictly before the horizon
is bounded by the source dividend strategy's right-limit cumulative mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ s in paymentTimes σ ∩ Iio (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂dividendMeasure D ω) ≤
    ENNReal.ofReal (rightLimit D T ω) := by
  let μ : Measure ℝ := dividendMeasure D ω
  let s : Set ℝ := paymentTimes σ ∩ Iio (T : ℝ)
  have hs : MeasurableSet s := (paymentTimes_measurable σ).inter measurableSet_Iio
  have hsubset : s ⊆ Icc (0 : ℝ) (T : ℝ) := by
    intro u hu
    exact ⟨(paymentTimes_membership_to_nNReal_active σ u hu.1).1, le_of_lt hu.2⟩
  have hweight : ∀ u ∈ s,
      ENNReal.ofReal (Real.exp (-(q * u))) ≤ 1 := by
    intro u hu
    have hu : 0 ≤ u := (paymentTimes_membership_to_nNReal_active σ u hu.1).1
    have hreal : Real.exp (-(q * u)) ≤ 1 := Real.exp_le_one_iff.mpr (by
      nlinarith [mul_nonneg hq hu])
    calc
      ENNReal.ofReal (Real.exp (-(q * u))) ≤ ENNReal.ofReal 1 :=
        ENNReal.ofReal_le_ofReal hreal
      _ = 1 := by norm_num
  calc
    (∫⁻ u in s, ENNReal.ofReal (Real.exp (-(q * u))) ∂μ) ≤
        (∫⁻ u in s, (1 : ℝ≥0∞) ∂μ) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hs] with u hu
      exact hweight u hu
    _ = μ s := by simp
    _ ≤ μ (Icc (0 : ℝ) (T : ℝ)) := measure_mono hsubset
    _ = ENNReal.ofReal (rightLimit D T ω) :=
      avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω T
