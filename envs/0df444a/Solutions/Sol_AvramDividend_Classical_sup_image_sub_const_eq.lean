-- Prove2me | solution 1 for AvramDividend.Classical.sup_image_sub_const_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T12:30:46.850254+00:00
-- url     : https://prove2.me/submissions/12c74a2c-d827-4942-b4d8-3355eb8dbc3b

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Translation of a bounded nonempty real set commutes with taking its supremum. -/
theorem solution
    (S : Set ℝ) (c : ℝ) (hne : S.Nonempty) (hb : BddAbove S) :
    sSup ((fun z : ℝ => z - c) '' S) = sSup S - c := by
  have hb' : BddAbove ((fun z : ℝ => z - c) '' S) := by
    obtain ⟨M, hM⟩ := hb
    refine ⟨M - c, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact sub_le_sub_right (hM hx) c
  apply le_antisymm
  · apply csSup_le (hne.image (fun z : ℝ => z - c))
    rintro y ⟨x, hx, rfl⟩
    exact sub_le_sub_right (le_csSup hb hx) c
  · apply sub_le_iff_le_add.mpr
    apply csSup_le hne
    intro x hx
    have hle : x - c ≤ sSup ((fun z : ℝ => z - c) '' S) :=
      le_csSup hb' ⟨x, hx, rfl⟩
    linarith
