-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_discounted_masked_compact_Hessian_uniform_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T17:56:31.292913+00:00
-- url     : https://prove2.me/submissions/d2c8558e-e66f-43bf-89ab-cc838f425af6

import Theorems.Thm_AvramDividend_Classical_avram_ga_compact_band_continuous_second_deriv_abs_bounded
import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology MeasureTheory AvramDividend.Classical
open scoped NNReal
theorem solution
    {Ω : Type*} (w : ℝ → ℝ) (a b q : ℝ) (hq : 0 ≤ q)
    (hCont : ContinuousOn (fun y => iteratedDeriv 2 w y) (Icc a b))
    (Y : ℕ → ℕ → Ω → ℝ) (s : ℕ → ℕ → ℝ≥0)
    (mask : ℕ → ℕ → Ω → Prop)
    (hFloor : ∀ m i ω, mask m i ω → a ≤ Y m i ω) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m i ω, mask m i ω →
      |Real.exp (-(q * (s m i : ℝ))) *
        (if Y m i ω ≤ b then iteratedDeriv 2 w (Y m i ω) else 0)| ≤ K  := by
  obtain ⟨K, hK, hB⟩ :=
    avram_ga_compact_band_continuous_second_deriv_abs_bounded w a b hCont
  refine ⟨K, hK, ?_⟩
  intro m i ω hm
  by_cases hy : Y m i ω ≤ b
  · have hd : |iteratedDeriv 2 w (Y m i ω)| ≤ K :=
      hB _ ⟨hFloor m i ω hm, hy⟩
    have hqtime : 0 ≤ q * (s m i : ℝ) :=
      mul_nonneg hq (NNReal.coe_nonneg _)
    have he : Real.exp (-(q * (s m i : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqtime)
    have hpos : 0 ≤ Real.exp (-(q * (s m i : ℝ))) :=
      (Real.exp_pos _).le
    calc
      _ = Real.exp (-(q * (s m i : ℝ))) *
          |iteratedDeriv 2 w (Y m i ω)| := by
        simp only [if_pos hy, abs_mul, abs_of_nonneg hpos]
      _ ≤ |iteratedDeriv 2 w (Y m i ω)| := by
        simpa only [one_mul] using
          (mul_le_mul_of_nonneg_right he (abs_nonneg _))
      _ ≤ K := hd
  · simpa only [if_neg hy, mul_zero, abs_zero] using hK
