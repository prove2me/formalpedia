-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_localised_finite_nonlin_jump_variation_le_marks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:53:07.198122+00:00
-- url     : https://prove2.me/submissions/007b27db-db6b-4a49-8b9c-b8edd4c2ee3b

import Mathlib
import Mathlib.Analysis.Normed.Group.Uniform
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

/-- Each finite collection of controlled original-source BV jump increments
is dominated by the total absolute mark variation on its compact localisation. -/
theorem solution {ι : Type*} (s : Finset ι)
    (w : ℝ → ℝ) (K : ℝ≥0) (a b δ : ℝ)
    (u z : ι → ℝ) (hδ : 0 ≤ δ)
    (hLip : LipschitzOnWith K w (Icc a b))
    (hu : ∀ i ∈ s, u i ∈ Icc (a + δ) b)
    (hz : ∀ i ∈ s, z i ∈ Icc (-δ) 0) :
    s.sum (fun i => |w (u i + z i) - w (u i)|) ≤
      (K : ℝ) * s.sum (fun i => |z i|) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hui : u i ∈ Icc a b := by
    rcases hu i hi with ⟨hlo, hhi⟩
    exact ⟨by linarith, hhi⟩
  have huzi : u i + z i ∈ Icc a b := by
    rcases hu i hi with ⟨hlo, hhi⟩
    rcases hz i hi with ⟨hzlo, hzhi⟩
    exact ⟨by linarith, by linarith⟩
  have h := hLip.norm_sub_le huzi hui
  simpa [Real.norm_eq_abs, add_sub_cancel_left] using h
