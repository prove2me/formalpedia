-- Prove2me | solution 1 for AvramDividend.Classical.shiftedSup_increment_eq_sup_sub
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:36:40.301685+00:00
-- url     : https://prove2.me/submissions/b4cf5bc6-641c-4ef1-841a-d6966c62659f

import Mathlib.Data.NNReal.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

/-- Translation of the running-record image commutes with the real supremum. -/
theorem solution
    (f : ℝ≥0 → ℝ) (u t : ℝ≥0)
    (hb : BddAbove ((fun r : ℝ≥0 => f (u + r)) '' Set.Icc 0 t)) :
    sSup ((fun r : ℝ≥0 => f (u + r) - f u) '' Set.Icc 0 t) =
      sSup ((fun r : ℝ≥0 => f (u + r)) '' Set.Icc 0 t) - f u := by
  let S : Set ℝ := (fun r : ℝ≥0 => f (u + r)) '' Set.Icc 0 t
  have hne : S.Nonempty := by
    refine ⟨f u, ?_⟩
    exact ⟨0, by simp, by simp⟩
  have hImage :
      ((fun z : ℝ => z - f u) '' S) =
      ((fun r : ℝ≥0 => f (u + r) - f u) '' Set.Icc 0 t) := by
    dsimp [S]
    rw [Set.image_image]
  rw [← hImage]
  have hb' : BddAbove ((fun z : ℝ => z - f u) '' S) := by
    obtain ⟨M, hM⟩ := hb
    refine ⟨M - f u, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact sub_le_sub_right (hM hz) (f u)
  apply le_antisymm
  · apply csSup_le (hne.image (fun z : ℝ => z - f u))
    rintro y ⟨z, hz, rfl⟩
    exact sub_le_sub_right (le_csSup hb hz) (f u)
  · apply sub_le_iff_le_add.mpr
    apply csSup_le hne
    intro z hz
    have hle : z - f u ≤ sSup ((fun v : ℝ => v - f u) '' S) :=
      le_csSup hb' ⟨z, hz, rfl⟩
    linarith
