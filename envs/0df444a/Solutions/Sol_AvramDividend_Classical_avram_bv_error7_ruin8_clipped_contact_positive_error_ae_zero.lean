-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_ruin8_clipped_contact_positive_error_ae_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:25:19.882058+00:00
-- url     : https://prove2.me/submissions/89f691a7-9e5d-4333-9d59-ef34088f3325

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_nonnegative_ruin_clip_contact_increment_le_raw
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_ruin8_uniform_contact_value_differences_vanish

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

/-- Uniform contact continuity plus zero-clipping turns vanishing raw
increments into vanishing positive errors, including ruin-crossing cells. -/
theorem solution
    (f : ℝ → ℝ) (B : ℝ) (hUC : UniformContinuousOn f (Set.Icc 0 B))
    (z c Err : ℕ → ℝ)
    (hBand : ∀ m, z m ∈ Set.Icc 0 B ∧ max (z m + c m) 0 ∈ Set.Icc 0 B)
    (hcTo : Tendsto c atTop (nhds (0 : ℝ)))
    (hMajorant : ∀ m,
      max (Err m) 0 ≤ max (f (max (z m + c m) 0) - f (z m)) 0) :
    Tendsto (fun m => max (Err m) 0) atTop (nhds (0 : ℝ)) := by
  have hcClip : Tendsto (fun m => max (z m + c m) 0 - z m)
      atTop (nhds (0 : ℝ)) := by
    apply (Metric.tendsto_atTop).2
    intro ε hε
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop).1 hcTo ε hε
    refine ⟨N, ?_⟩
    intro m hm
    have hraw : |c m| < ε := by
      simpa [Real.dist_eq] using hN m hm
    have hclip := avram_bv_error7_ruin8_nonnegative_ruin_clip_contact_increment_le_raw
      (z m) (c m) (hBand m).1.1
    simpa [Real.dist_eq] using lt_of_le_of_lt hclip hraw
  have hClipBand (m : ℕ) :
      z m + (max (z m + c m) 0 - z m) ∈ Set.Icc 0 B := by
    convert (hBand m).2 using 1 <;> ring
  have hValue := avram_bv_error7_ruin8_uniform_contact_value_differences_vanish
    f (Set.Icc 0 B) hUC z
    (fun m => max (z m + c m) 0 - z m)
    (fun m => (hBand m).1) hClipBand hcClip
  have hEq (m : ℕ) :
      z m + (max (z m + c m) 0 - z m) = max (z m + c m) 0 := by ring
  simp only [hEq] at hValue
  apply (Metric.tendsto_atTop).2
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop).1 hValue ε hε
  refine ⟨N, ?_⟩
  intro m hm
  have hsmall : |f (max (z m + c m) 0) - f (z m)| < ε := by
    simpa [Real.dist_eq] using hN m hm
  have hnonneg : 0 ≤ max (Err m) 0 := le_max_right _ _
  have hbound : max (f (max (z m + c m) 0) - f (z m)) 0 ≤
      |f (max (z m + c m) 0) - f (z m)| :=
    max_le (le_abs_self _) (abs_nonneg _)
  calc
    dist (max (Err m) 0) (0 : ℝ) = max (Err m) 0 := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
    _ ≤ max (f (max (z m + c m) 0) - f (z m)) 0 := hMajorant m
    _ ≤ |f (max (z m + c m) 0) - f (z m)| := hbound
    _ < ε := hsmall
