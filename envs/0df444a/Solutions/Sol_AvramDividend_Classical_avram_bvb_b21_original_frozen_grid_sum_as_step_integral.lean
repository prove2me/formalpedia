-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b21_original_frozen_grid_sum_as_step_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T17:56:22.439342+00:00
-- url     : https://prove2.me/submissions/f26d2edf-acee-41c3-9439-1c972a7596b1

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped ENNReal
noncomputable section

/-- Finite-grid frozen losses are exactly integrals of their step kernel. -/
theorem solution (N : ℕ) (u c : ℕ → ℝ)
    (hu : ∀ i < N, u i ≤ u (i + 1)) :
    (∫ t : ℝ, ∑ i ∈ Finset.range N,
      (Ico (u i) (u (i + 1))).indicator (fun _ => c i) t) =
      ∑ i ∈ Finset.range N, (u (i + 1) - u i) * c i := by
  have hintegrable (i : ℕ) :
      Integrable ((Ico (u i) (u (i + 1))).indicator (fun _ : ℝ => c i)) volume := by
    have hfinite : volume (Ico (u i) (u (i + 1))) ≠ ⊤ := by
      simp [Real.volume_Ico]
    exact (integrableOn_const (s := Ico (u i) (u (i + 1)))
      (μ := volume) hfinite).integrable_indicator measurableSet_Ico
  rw [integral_finsetSum (Finset.range N) (by
    intro i hi
    exact hintegrable i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_indicator_const (c i) measurableSet_Ico]
  rw [Real.volume_real_Ico_of_le (hu i (Finset.mem_range.mp hi))]
  simp only [smul_eq_mul]
