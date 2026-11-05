-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_random_stopped_uniform_band_kernel_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:46:17.681975+00:00
-- url     : https://prove2.me/submissions/2dfeac57-f6fa-43d6-a1bd-973370683092

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
/-- The same deterministic derivative bound controls the original source
dividend-gradient kernel at every sample-dependent finite stopping clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0) (ν : Ω → Measure ℝ)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (a b K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ y ∈ Icc a b, |deriv w y| ≤ K)
    (hstate : ∀ ω, ∀ᵐ s ∂(ν ω).restrict
      (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
        rightLimit D s.toNNReal ω ∈ Icc a b) :
    ∀ ω, ∀ᵐ s ∂(ν ω).restrict (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)),
      ‖Real.exp (-(q * s)) *
        (1 - deriv w (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω)
          s.toNNReal - rightLimit D s.toNNReal ω))‖ ≤ 1 + K := by
  intro ω
  let S : Set ℝ := paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)
  have hset : MeasurableSet S :=
    (paymentTimes_measurable (σ ω)).inter measurableSet_Iic
  have hmem : ∀ᵐ s ∂(ν ω).restrict S, s ∈ S := ae_restrict_mem hset
  filter_upwards [hstate ω, hmem] with s hs hsmem
  have hs0 : 0 ≤ s :=
    (paymentTimes_membership_to_nNReal_active (σ ω) s hsmem.1).1
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
