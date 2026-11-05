-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_dominated_diffuse_compact_band_discounted_signed_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:39:33.494103+00:00
-- url     : https://prove2.me/submissions/ef92fb6d-2251-4213-b16a-067f1087efa1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_compact_interior_derivative_bound
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The true original diffuse Stieltjes submeasure admits an integrable
discounted derivative correction on compact strictly interior reserves;
right-payment atoms may lie at zero or cap without affecting the hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (ν : Measure ℝ) (hdom : ν ≤ dividendMeasure D ω)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hSM : AEStronglyMeasurable (fun s : ℝ => Real.exp (-(q * s)) *
      (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
        s.toNNReal - rightLimit D s.toNNReal ω)))
      (ν.restrict (paymentTimes σ ∩ Iic (T : ℝ))))
    (hstate : ∀ᵐ s ∂ν.restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω ∈ Icc a b) :
    IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
      (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω)))
      (paymentTimes σ ∩ Iic (T : ℝ)) ν := by
  obtain ⟨K, hK0, hK⟩ :=
    avram_p4_d_dividend_ubv_compact_interior_derivative_bound
      C w hwC2 a b hab hBand
  let S : Set ℝ := paymentTimes σ ∩ Iic (T : ℝ)
  have hsubset : S ⊆ Icc (0 : ℝ) (T : ℝ) := by
    intro u hu
    exact ⟨(paymentTimes_membership_to_nNReal_active σ u hu.1).1, hu.2⟩
  have hmass : ν S < ⊤ := by
    calc
      ν S ≤ (dividendMeasure D ω) S := hdom S
      _ ≤ (dividendMeasure D ω) (Icc (0 : ℝ) (T : ℝ)) := measure_mono hsubset
      _ = ENNReal.ofReal (rightLimit D T ω) :=
        avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω T
      _ < ⊤ := ENNReal.ofReal_lt_top
  let z : ℝ → ℝ := fun s => x + Function.leftLim
    (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω
  let f : ℝ → ℝ := fun s => Real.exp (-(q * s)) * (1 - deriv w (z s))
  have hset : MeasurableSet S :=
    (paymentTimes_measurable σ).inter measurableSet_Iic
  have hmem : ∀ᵐ s ∂ν.restrict S, s ∈ S := ae_restrict_mem hset
  have hbound : ∀ᵐ s ∂ν.restrict S, ‖f s‖ ≤ 1 + K := by
    filter_upwards [hstate, hmem] with s hs hsmem
    have hs0 : 0 ≤ s :=
      (paymentTimes_membership_to_nNReal_active σ s hsmem.1).1
    have he : Real.exp (-(q * s)) ≤ 1 :=
      (Real.exp_le_one_iff).2 (neg_nonpos.mpr (mul_nonneg hq hs0))
    have hder := hK _ hs
    have htri : |1 - deriv w (z s)| ≤ 1 + K := by
      calc
        |1 - deriv w (z s)| ≤ |(1 : ℝ)| + |deriv w (z s)| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            (abs_add_le (1 : ℝ) (-(deriv w (z s))))
        _ = 1 + |deriv w (z s)| := by norm_num
        _ ≤ 1 + K := add_le_add_right hder 1
    have hK1 : 0 ≤ 1 + K := by linarith
    change |Real.exp (-(q * s)) * (1 - deriv w (z s))| ≤ 1 + K
    calc
      |Real.exp (-(q * s)) * (1 - deriv w (z s))| =
          Real.exp (-(q * s)) * |1 - deriv w (z s)| := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-(q * s)) * (1 + K) :=
        mul_le_mul_of_nonneg_left htri (le_of_lt (Real.exp_pos _))
      _ ≤ 1 * (1 + K) := mul_le_mul_of_nonneg_right he hK1
      _ = 1 + K := one_mul _
  exact IntegrableOn.of_bound hmass hSM (1 + K) hbound
