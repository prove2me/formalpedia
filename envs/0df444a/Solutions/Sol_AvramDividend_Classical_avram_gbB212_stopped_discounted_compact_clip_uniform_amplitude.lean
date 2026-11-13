-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB212_stopped_discounted_compact_clip_uniform_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:48:12.201471+00:00
-- url     : https://prove2.me/submissions/94eaecc0-8848-4457-9e5f-11d92e55ab74

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Theorems.Thm_AvramDividend_Classical_avram_gbB210_continuous_gradient_compact_clip_uniform_abs_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Discount and random time restriction preserve the compact clipped gradient bound. -/
theorem solution
    {Ω : Type*} (w : ℝ → ℝ) (a b : ℝ)
    (hContinuous : ContinuousOn (deriv w) (Icc a b))
    (q : ℝ) (hq : 0 ≤ q)
    (Y : ℝ≥0 → Ω → ℝ) (ρ : Ω → ℝ≥0) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (s : ℝ≥0) (ω : Ω),
        |if s < ρ ω then Real.exp (-(q * (s : ℝ))) *
          (if Y s ω ∈ Icc a b then deriv w (Y s ω) else 1)
        else 0| ≤ B := by
  obtain ⟨B, hB, hClip⟩ :=
    avram_gbB210_continuous_gradient_compact_clip_uniform_abs_bound
      w a b hContinuous
  refine ⟨B, hB, ?_⟩
  intro s ω
  by_cases hs : s < ρ ω
  · simp only [if_pos hs]
    have hExp : Real.exp (-(q * (s : ℝ))) ≤ 1 := by
      apply (Real.exp_le_one_iff).2
      have hnonneg : 0 ≤ q * (s : ℝ) :=
        mul_nonneg hq (NNReal.coe_nonneg s)
      linarith
    calc
      |Real.exp (-(q * (s : ℝ))) *
        (if Y s ω ∈ Icc a b then deriv w (Y s ω) else 1)| =
          Real.exp (-(q * (s : ℝ))) *
          |if Y s ω ∈ Icc a b then deriv w (Y s ω) else 1| := by
            rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
      _ ≤ Real.exp (-(q * (s : ℝ))) * B := by
        exact mul_le_mul_of_nonneg_left (hClip (Y s ω))
          (Real.exp_nonneg _)
      _ ≤ 1 * B := by
        exact mul_le_mul_of_nonneg_right hExp hB
      _ = B := one_mul _
  · simpa only [if_neg hs, abs_zero] using hB

