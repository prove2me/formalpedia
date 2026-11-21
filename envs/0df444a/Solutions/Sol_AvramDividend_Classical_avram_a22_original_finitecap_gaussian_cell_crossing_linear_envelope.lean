-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_finitecap_gaussian_cell_crossing_linear_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:21:42.484486+00:00
-- url     : https://prove2.me/submissions/446ca667-70b5-40db-b8bc-5307bbdf68f8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_finitecap_caplinear_global_gaussian_growth
open Set AvramDividend.Classical

theorem solution
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y r : ℝ,
      0 ≤ y → y ≤ b →
      |if y + r ≤ b then w (y + r)
       else w b + (y + r - b)| ≤ K + b + |r|  := by
  obtain ⟨K, hK, hBound⟩ :=
    avram_a22_original_finitecap_caplinear_global_gaussian_growth
      w b hb hw_cont hw_neg
  refine ⟨K, hK, ?_⟩
  intro y r hy0 hyb
  have hV := hBound (y + r)
  have hTri := abs_add_le y r
  rw [abs_of_nonneg hy0] at hTri
  linarith
