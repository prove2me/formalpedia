-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_compact_band_true_stopped_discounted_signed_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:37:39.06061+00:00
-- url     : https://prove2.me/submissions/438556a7-31a8-4931-8c8c-580d8dc1b21b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_compact_interior_derivative_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_bounded_signed_stieltjes_integrableOn
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- For the exact original stopped payment set, interior C² regularity gives
the discounted signed dividend-gradient kernel an integrable envelope.
Negative times are excluded by the true paymentTimes predicate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hSM : AEStronglyMeasurable
      (fun s : ℝ => Real.exp (-(q * s)) *
        (1 - deriv w (x +
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω)))
      ((dividendMeasure D ω).restrict
        (paymentTimes σ ∩ Iic (T : ℝ))))
    (hstate : ∀ᵐ s ∂(dividendMeasure D ω).restrict
        (paymentTimes σ ∩ Iic (T : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b) :
    IntegrableOn (fun s : ℝ => Real.exp (-(q * s)) *
      (1 - deriv w (x +
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω)))
      (paymentTimes σ ∩ Iic (T : ℝ)) (dividendMeasure D ω) := by
  obtain ⟨K, hK0, hK⟩ :=
    avram_p4_d_dividend_ubv_compact_interior_derivative_bound
      C w hwC2 a b hab hBand
  have hSet : MeasurableSet (paymentTimes σ ∩ Iic (T : ℝ)) :=
    (paymentTimes_measurable σ).inter measurableSet_Iic
  have hmem : ∀ᵐ s ∂(dividendMeasure D ω).restrict
      (paymentTimes σ ∩ Iic (T : ℝ)),
      s ∈ paymentTimes σ ∩ Iic (T : ℝ) := ae_restrict_mem hSet
  apply avram_p4_d_dividend_original_true_stopped_bounded_signed_stieltjes_integrableOn
    D hD ω σ T _ hSM (1 + K)
  filter_upwards [hstate, hmem] with s hs hsmem
  have hs0 : 0 ≤ s :=
    (paymentTimes_membership_to_nNReal_active σ s hsmem.1).1
  have hqns : -(q * s) ≤ 0 := neg_nonpos.mpr (mul_nonneg hq hs0)
  have he : Real.exp (-(q * s)) ≤ 1 := (Real.exp_le_one_iff).2 hqns
  have hder := hK _ hs
  have htri : |1 - deriv w (x +
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
      rightLimit D s.toNNReal ω)| ≤ 1 + K := by
    calc
      |1 - deriv w (x +
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω)| =
          |(1 : ℝ) + -(deriv w (x +
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
            rightLimit D s.toNNReal ω))| := by rw [sub_eq_add_neg]
      _ ≤ |(1 : ℝ)| + |-(deriv w (x +
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω))| := abs_add_le _ _
      _ = 1 + |deriv w (x +
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω)| := by simp
      _ ≤ 1 + K := add_le_add_right hder 1
  have hK1 : 0 ≤ 1 + K := by linarith
  simp only [Real.norm_eq_abs]
  calc
    |Real.exp (-(q * s)) * (1 - deriv w (x +
      Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
      rightLimit D s.toNNReal ω))| =
        Real.exp (-(q * s)) * |1 - deriv w (x +
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω)| := by
            rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-(q * s)) * (1 + K) :=
      mul_le_mul_of_nonneg_left htri (le_of_lt (Real.exp_pos _))
    _ ≤ 1 * (1 + K) := mul_le_mul_of_nonneg_right he hK1
    _ = 1 + K := one_mul _
