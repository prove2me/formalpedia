-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_real_stopped_cash_le_original_total_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:32:34.86947+00:00
-- url     : https://prove2.me/submissions/02d5ddb0-45fc-4474-bc97-9b3113038cab

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_bounded_kernel_cash_le_total_mass

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- True real discounted stopped Cash is nonnegative and bounded by original finite total mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) (Cash : ℝ)
    (hCash : Cash =
      (∫⁻ s in paymentTimes σ ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    0 ≤ Cash ∧
      Cash ≤ (ENNReal.ofReal (rightLimit D T ω)).toReal := by
  have hweight : ∀ u ∈ paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * u))) ≤ 1 := by
    intro u hu
    have hu : 0 ≤ u := (paymentTimes_membership_to_nNReal_active σ u hu.1).1
    have hreal : Real.exp (-(q * u)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hq hu])
    calc
      ENNReal.ofReal (Real.exp (-(q * u))) ≤ ENNReal.ofReal 1 :=
        ENNReal.ofReal_le_ofReal hreal
      _ = 1 := by norm_num
  have hbound :=
    avram_p4_d_dividend_original_stopped_bounded_kernel_cash_le_total_mass
      D hD ω σ T (fun u => ENNReal.ofReal (Real.exp (-(q * u)))) hweight
  rw [hCash]
  exact ⟨ENNReal.toReal_nonneg,
    ENNReal.toReal_mono (ne_top_of_lt ENNReal.ofReal_lt_top) hbound⟩
