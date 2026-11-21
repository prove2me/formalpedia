-- Prove2me | solution 1 for AvramDividend.Classical.avram_a22_original_finitecap_caplinear_global_gaussian_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T08:23:03.939167+00:00
-- url     : https://prove2.me/submissions/4af025d0-7c94-4383-87a4-9c553a9446b4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_finitecap_candidate_compact_absolute_bound
import Theorems.Thm_AvramDividend_Classical_avram_a22_original_caplinear_linear_growth_of_compact_candidate_bound
open Set AvramDividend.Classical

theorem solution
    (w : ℝ → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ,
      |if z ≤ b then w z else w b + (z - b)| ≤ K + |z|  := by
  have hIcc : ContinuousOn w (Icc 0 b) :=
    hw_cont.mono (by
      intro z hz
      exact hz.1)
  obtain ⟨K, hK, hBound⟩ :=
    avram_a22_original_finitecap_candidate_compact_absolute_bound
      w b hb hIcc
  refine ⟨K, hK, ?_⟩
  intro z
  exact avram_a22_original_caplinear_linear_growth_of_compact_candidate_bound
    w b K hb hK hw_neg hBound z
