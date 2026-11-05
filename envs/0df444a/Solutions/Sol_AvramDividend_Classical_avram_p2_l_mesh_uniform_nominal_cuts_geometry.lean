-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_l_mesh_uniform_nominal_cuts_geometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:59:07.668944+00:00
-- url     : https://prove2.me/submissions/20142fb7-816a-4522-8298-fce290c0ef7e

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

/-- Positive real cell lengths produce ordered, equally spaced finite cuts. -/
theorem solution (n : ℕ) (A h : ℝ) (hh : 0 < h) :
    StrictMono (fun i : Fin (n + 1) => A + (i.val : ℝ) * h) ∧
    (∀ i : Fin n,
      (A + (i.succ.val : ℝ) * h) -
        (A + (i.castSucc.val : ℝ) * h) = h) ∧
    (A + ((0 : Fin (n + 1)).val : ℝ) * h) = A ∧
    (A + ((Fin.last n).val : ℝ) * h) = A + (n : ℝ) * h := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hv : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    have hmul := mul_lt_mul_of_pos_right hv hh
    dsimp
    linarith
  · intro i
    simp only [Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
    ring
  · simp
  · simp [Fin.val_last]
