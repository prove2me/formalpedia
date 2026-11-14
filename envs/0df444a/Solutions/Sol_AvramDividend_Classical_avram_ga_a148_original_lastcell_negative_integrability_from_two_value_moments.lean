-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a148_original_lastcell_negative_integrability_from_two_value_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T12:21:41.292366+00:00
-- url     : https://prove2.me/submissions/3696e6db-b541-4e0c-9c80-171f2d195874

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
noncomputable section

/-- The actual Gaussian last-cell negative part is integrable when its two stopped spatial source-value moments are integrable. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E A B : ℕ → Ω → ℝ) (mask : Ω → Prop)
    [DecidablePred mask]
    (hE : ∀ m ω, 0 ≤ E m ω ∧ E m ω ≤ 1)
    (hAI : ∀ m, Integrable (fun ω => if mask ω then |A m ω| else 0) P)
    (hBI : ∀ m, Integrable (fun ω => if mask ω then |B m ω| else 0) P)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => if mask ω then max (-(E m ω * (A m ω - B m ω))) 0 else 0) P) :
    ∀ m, Integrable
      (fun ω => if mask ω then max (-(E m ω * (A m ω - B m ω))) 0 else 0) P := by
  intro m
  have hBound (ω : Ω) :
      ‖(if mask ω then max (-(E m ω * (A m ω - B m ω))) 0 else 0 : ℝ)‖ ≤
        (if mask ω then |A m ω| else 0) +
          (if mask ω then |B m ω| else 0) := by
    by_cases hm : mask ω
    · simp only [if_pos hm]
      obtain ⟨h0,h1⟩ := hE m ω
      have hAbs : |A m ω - B m ω| ≤ |A m ω| + |B m ω| :=
        abs_sub _ _
      have hProd : |E m ω * (A m ω - B m ω)| ≤
          |A m ω - B m ω| := by
        rw [abs_mul, abs_of_nonneg h0]
        nlinarith [mul_le_mul_of_nonneg_right h1 (abs_nonneg (A m ω - B m ω))]
      have hMax : max (-(E m ω * (A m ω - B m ω))) 0 ≤
          |E m ω * (A m ω - B m ω)| := by
        exact max_le (neg_le_abs _) (abs_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      linarith
    · simp only [if_neg hm, norm_zero, add_zero, le_refl]
  exact Integrable.mono' ((hAI m).add (hBI m)) (hMeas m)
    (Filter.Eventually.of_forall hBound)
