-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f12_masked_mean_budget_iff_positive_clock_excess_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:26:34.857263+00:00
-- url     : https://prove2.me/submissions/ca81a3d0-b852-4208-a7ee-5546c3f64c4b

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_positive_clock_mask_residual_identity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

/-- The physical masked mean budget is exactly a positive-clock excess sign. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (A : Set Ω) (hA : MeasurableSet A)
    [DecidablePred (fun ω : Ω => ω ∈ A)]
    (F : Ω → ℝ) (hF : Integrable F P) (b : ℝ) :
    (∫ ω, (if ω ∈ A then b else F ω) ∂P) ≤ b ↔
      (∫ ω in Aᶜ, F ω - b ∂P) ≤ 0 := by
  have hb : Integrable (fun _ : Ω => b) P := integrable_const b
  have hI : Integrable (A.indicator (fun ω => b - F ω)) P :=
    (hb.sub hF).indicator hA
  have hFun : (fun ω => if ω ∈ A then b else F ω) =
      (fun ω => F ω + A.indicator (fun ω => b - F ω) ω) := by
    funext ω
    by_cases h : ω ∈ A
    · simp [Set.indicator, h] <;> ring
    · simp [Set.indicator, h] <;> ring
  have hMask : Integrable (fun ω => if ω ∈ A then b else F ω) P := by
    rw [hFun]
    exact hF.add hI
  have hIdentity :=
    avram_p4_f12_positive_clock_mask_residual_identity P A hA F hF b
  rw [integral_sub hMask hb] at hIdentity
  have hConst : (∫ _ω : Ω, b ∂P) = b := by simp
  rw [hConst] at hIdentity
  constructor
  · intro h
    rw [← hIdentity]
    linarith
  · intro h
    rw [← hIdentity] at h
    linarith
