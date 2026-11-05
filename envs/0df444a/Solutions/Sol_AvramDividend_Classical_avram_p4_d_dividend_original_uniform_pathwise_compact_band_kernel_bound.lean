-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_uniform_pathwise_compact_band_kernel_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:38:12.522484+00:00
-- url     : https://prove2.me/submissions/064b1094-031b-452e-8be9-cf07b7a2ecf0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- One deterministic derivative constant bounds the genuine stopped source
dividend-gradient kernel on every path in the same interior band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : ℝ≥0∞) (T : ℝ≥0) (ν : Ω → Measure ℝ)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (a b K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ y ∈ Icc a b, |deriv w y| ≤ K)
    (hstate : ∀ ω, ∀ᵐ s ∂(ν ω).restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b) :
    ∀ ω, ∀ᵐ s ∂(ν ω).restrict (paymentTimes σ ∩ Iic (T : ℝ)),
      ‖Real.exp (-(q * s)) *
        (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
          s.toNNReal - rightLimit D s.toNNReal ω))‖ ≤ 1 + K := by
  intro ω
  let S : Set ℝ := paymentTimes σ ∩ Iic (T : ℝ)
  have hset : MeasurableSet S :=
    (paymentTimes_measurable σ).inter measurableSet_Iic
  have hmem : ∀ᵐ s ∂(ν ω).restrict S, s ∈ S := ae_restrict_mem hset
  filter_upwards [hstate ω, hmem] with s hs hsmem
  have hs0 : 0 ≤ s :=
    (paymentTimes_membership_to_nNReal_active σ s hsmem.1).1
  have he : Real.exp (-(q * s)) ≤ 1 :=
    (Real.exp_le_one_iff).2 (neg_nonpos.mpr (mul_nonneg hq hs0))
  have hder := hK _ hs
  have htri : |1 - deriv w (x + Function.leftLim
      (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω)| ≤
      1 + K := by
    calc
      |1 - deriv w (x + Function.leftLim
          (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω)| ≤
          |(1 : ℝ)| + |deriv w (x + Function.leftLim
            (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          (abs_add_le (1 : ℝ) (-(deriv w (x + Function.leftLim
            (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω))))
      _ = 1 + |deriv w (x + Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω)| := by norm_num
      _ ≤ 1 + K := add_le_add_right hder 1
  have hK1 : 0 ≤ 1 + K := by linarith
  change |Real.exp (-(q * s)) *
    (1 - deriv w (x + Function.leftLim
      (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω))| ≤ 1 + K
  calc
    _ = Real.exp (-(q * s)) * |1 - deriv w (x + Function.leftLim
        (fun r : ℝ≥0 => X.X r ω) s.toNNReal - rightLimit D s.toNNReal ω)| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-(q * s)) * (1 + K) :=
      mul_le_mul_of_nonneg_left htri (le_of_lt (Real.exp_pos _))
    _ ≤ 1 * (1 + K) := mul_le_mul_of_nonneg_right he hK1
    _ = 1 + K := one_mul _
