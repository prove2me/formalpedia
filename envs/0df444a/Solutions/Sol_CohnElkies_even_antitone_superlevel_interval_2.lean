-- Prove2me | solution 2 for CohnElkies.even_antitone_superlevel_interval
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:24:35.336553+00:00
-- url     : https://prove2.me/submissions/31891be7-7504-437c-afc8-c0eeeb724fdf

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology


theorem solution
    {f : ℝ → ℝ} {B t : ℝ}
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hanti : AntitoneOn f (Ici (0 : ℝ)))
    (hsupport : Function.support f ⊆ Icc (-B) B)
    (ht : 0 < t) :
    ∃ r : ℝ, 0 ≤ r ∧
      Ioo (-r) r ⊆ {x : ℝ | t < f x} ∧
        {x : ℝ | t < f x} ⊆ Icc (-r) r := by
  set S := {x : ℝ | 0 ≤ x ∧ t < f x} with hSdef
  have hpos : ∀ x, t < f x → x ∈ Icc (-B) B := fun x hx =>
    hsupport (show f x ≠ 0 from by intro h; rw [h] at hx; linarith)
  have hbdd : BddAbove S := ⟨B, fun x hx => (hpos x hx.2).2⟩
  have habs : ∀ x, f x = f |x| := by
    intro x; rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, heven]
  refine ⟨sSup S, ?_, ?_, ?_⟩
  · by_cases hne : S.Nonempty
    · obtain ⟨y, hy⟩ := hne; exact le_trans hy.1 (le_csSup hbdd hy)
    · rw [Set.not_nonempty_iff_eq_empty.1 hne, Real.sSup_empty]
  · intro x hx
    have hx' : |x| < sSup S := abs_lt.2 ⟨hx.1, hx.2⟩
    have hne : S.Nonempty := by
      by_contra hne
      rw [Set.not_nonempty_iff_eq_empty.1 hne, Real.sSup_empty] at hx'
      linarith [abs_nonneg x]
    obtain ⟨y, hy, hxy⟩ := exists_lt_of_lt_csSup hne hx'
    show t < f x
    rw [habs x]
    exact lt_of_lt_of_le hy.2 (hanti (abs_nonneg x) hy.1 hxy.le)
  · intro x hx
    have hx2 : t < f x := hx
    have hm : |x| ∈ S := ⟨abs_nonneg x, by rw [← habs x]; exact hx2⟩
    have := le_csSup hbdd hm
    exact abs_le.1 this

