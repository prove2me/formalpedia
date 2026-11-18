-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB141_original_stopped_uniform_grid_prefix_length_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T19:05:44.722988+00:00
-- url     : https://prove2.me/submissions/51c5ac3c-a49f-4590-9be5-b05bcfd44b94

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB108_monotone_physical_grid_stop_mask_has_prefix_index
import Theorems.Thm_AvramDividend_Classical_avram_gbB63_original_finitegrid_prefix_mask_equals_short_range
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- A strict stopped uniform physical grid has occupied prefix length at most T+Δ. -/
theorem solution
    (s : ℕ → ℝ≥0) (hs : Monotone s) (hs0 : s 0 = 0)
    (Δ T : ℝ≥0) (hstep : ∀ i, s (i + 1) = s i + Δ)
    (m : ℕ) :
    (Finset.range (m + 1)).sum
      (fun i => if s i < T then (Δ : ℝ) else 0) ≤
      ((T + Δ : ℝ≥0) : ℝ) := by
  obtain ⟨k, hk, hiff⟩ :=
    avram_gbB108_monotone_physical_grid_stop_mask_has_prefix_index
      s hs T m
  have hform (i : ℕ) : s i = (i : ℝ≥0) * Δ := by
    induction i with
    | zero => simp [hs0]
    | succ i ih =>
        rw [hstep i, ih]
        push_cast
        ring
  have hsk : s k ≤ T + Δ := by
    cases k with
    | zero =>
        simpa [hs0] using (zero_le (T + Δ))
    | succ j =>
        have hj : j < m + 1 := by omega
        have hjT : s j < T := (hiff j hj).2 (by omega)
        rw [hstep j]
        simpa only [add_comm] using
          (add_le_add_right (le_of_lt hjT) Δ)
  have hsum :
      (Finset.range (m + 1)).sum
        (fun i => if s i < T then (Δ : ℝ) else 0) =
      (Finset.range k).sum (fun _ => (Δ : ℝ)) := by
    calc
      _ = (Finset.range (m + 1)).sum
          (fun i => if i < k then (Δ : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro i hi
            have h := hiff i (Finset.mem_range.mp hi)
            by_cases hit : s i < T
            · have hik := h.mp hit
              simp [hit, hik]
            · have hik : ¬ i < k := fun hi => hit (h.mpr hi)
              simp [hit, hik]
      _ = (Finset.range k).sum (fun _ => (Δ : ℝ)) :=
        avram_gbB63_original_finitegrid_prefix_mask_equals_short_range
          m k hk (fun _ => (Δ : ℝ))
  rw [hsum]
  have hreal : ((k : ℝ) * (Δ : ℝ)) ≤ ((T + Δ : ℝ≥0) : ℝ) := by
    have h := hsk
    rw [hform] at h
    exact_mod_cast h
  simpa using hreal
