-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_original_finitecap_gaussian_crossing_value_difference_linear_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T09:51:10.631584+00:00
-- url     : https://prove2.me/submissions/fc657c66-943f-4048-8318-aa6efbed0c03

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_finitecap_candidate_compact_absolute_bound
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_finitecap_gaussian_cell_crossing_linear_envelope
open Set AvramDividend.Classical
theorem solution
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y r : ℝ,
      0 ≤ y → y ≤ b →
      |(if y + r ≤ b then w (y + r)
         else w b + (y + r - b)) - w y| ≤ K + b + |r|  := by
  have hIcc : ContinuousOn w (Icc 0 b) :=
    hw_cont.mono (by intro z hz; exact hz.1)
  obtain ⟨K₁, hK₁, hBound⟩ :=
    avram_a22_original_finitecap_candidate_compact_absolute_bound
      w b hb hIcc
  obtain ⟨K₂, hK₂, hCross⟩ :=
    avram_a22_original_finitecap_gaussian_cell_crossing_linear_envelope
      w b hb hw_cont hw_neg
  refine ⟨K₁ + K₂, add_nonneg hK₁ hK₂, ?_⟩
  intro y r hy0 hyb
  have hV := hCross y r hy0 hyb
  have hW := hBound y hy0 hyb
  have hTri := abs_add_le
    (if y + r ≤ b then w (y + r) else w b + (y + r - b)) (-w y)
  simp only [abs_neg, ← sub_eq_add_neg] at hTri
  linarith
