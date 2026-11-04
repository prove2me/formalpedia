-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_localised_first_order_small_negative_mark_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:52:52.6101+00:00
-- url     : https://prove2.me/submissions/7c38cb94-53b0-48ea-9043-695c2b7d1ce7

import Mathlib
import Mathlib.Analysis.Normed.Group.Uniform
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

/-- A C¹ test function with a locally established Lipschitz constant has
the first-order small negative-jump envelope on the interior margin. -/
theorem solution (w : ℝ → ℝ) (K : ℝ≥0) (a b δ u z : ℝ)
    (hδ : 0 ≤ δ)
    (hLip : LipschitzOnWith K w (Icc a b))
    (hu : u ∈ Icc (a + δ) b)
    (hz : z ∈ Icc (-δ) 0) :
    |w (u + z) - w u| ≤ (K : ℝ) * |z| := by
  have hu' : u ∈ Icc a b := by
    rcases hu with ⟨hlo, hhi⟩
    exact ⟨by linarith, hhi⟩
  have huz : u + z ∈ Icc a b := by
    rcases hu with ⟨hlo, hhi⟩
    rcases hz with ⟨hzlo, hzhi⟩
    exact ⟨by linarith, by linarith⟩
  have h := hLip.norm_sub_le huz hu'
  simpa [Real.norm_eq_abs, add_sub_cancel_left] using h
