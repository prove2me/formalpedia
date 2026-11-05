-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_archimedean_positive_fine_cell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T11:05:54.248463+00:00
-- url     : https://prove2.me/submissions/50ebe3ea-a11a-4524-9226-6b289fd09df2

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

/-- A real interval admits positive uniform cells below any given radius. -/
theorem solution (A B δ : ℝ) (hAB : A < B) (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < (B - A) / ((n : ℝ) + 1) ∧
      (B - A) / ((n : ℝ) + 1) < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((B - A) / δ)
  have hden : 0 < (n : ℝ) + 1 := by positivity
  refine ⟨n, div_pos (sub_pos.mpr hAB) hden, ?_⟩
  apply (div_lt_iff₀ hden).2
  have hgap : B - A < (n : ℝ) * δ :=
    (div_lt_iff₀ hδ).1 hn
  nlinarith
