-- Prove2me | solution 1 for CohnElkies.even_antitone_superlevel_interval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:23.720106+00:00
-- url     : https://prove2.me/submissions/e1f76ac0-a423-41e3-b2a4-f4f9050a5138

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
namespace CohnElkies
theorem _root_.solution
    {f : ℝ → ℝ} {B t : ℝ}
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hanti : AntitoneOn f (Ici (0 : ℝ)))
    (hsupport : Function.support f ⊆ Icc (-B) B)
    (ht : 0 < t) :
    ∃ r : ℝ, 0 ≤ r ∧
      Ioo (-r) r ⊆ {x : ℝ | t < f x} ∧
        {x : ℝ | t < f x} ⊆ Icc (-r) r := by
  have habs (x : ℝ) : f |x| = f x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, heven]
  let S : Set ℝ := {u : ℝ | 0 ≤ u ∧ t < f u}
  by_cases hS : S.Nonempty
  · have hbdd : BddAbove S := by
      refine ⟨B, ?_⟩
      intro u hu
      change 0 ≤ u ∧ t < f u at hu
      have hunonzero : f u ≠ 0 := by
        intro hzero
        rw [hzero] at hu
        linarith [hu.2]
      exact (hsupport hunonzero).2
    let r : ℝ := sSup S
    have hr : 0 ≤ r := by
      obtain ⟨u, hu⟩ := hS
      have hu' : 0 ≤ u ∧ t < f u := hu
      exact le_trans hu'.1 (le_csSup hbdd hu)
    refine ⟨r, hr, ?_, ?_⟩
    · intro x hx
      have hxabs : |x| < r := abs_lt.mpr hx
      obtain ⟨u, hu, hxu⟩ :=
        exists_lt_of_lt_csSup hS hxabs
      have hu' : 0 ≤ u ∧ t < f u := hu
      have horder : f u ≤ f |x| :=
        hanti (show |x| ∈ Ici 0 from abs_nonneg x)
          (show u ∈ Ici 0 from hu'.1) hxu.le
      change t < f x
      rw [← habs]
      exact lt_of_lt_of_le hu'.2 horder
    · intro x hx
      have hxS : |x| ∈ S := by
        change 0 ≤ |x| ∧ t < f |x|
        refine ⟨abs_nonneg x, ?_⟩
        rw [habs]
        exact hx
      have hxle : |x| ≤ r := le_csSup hbdd hxS
      exact (abs_le.mp hxle)
  · refine ⟨0, le_rfl, ?_, ?_⟩
    · simp
    · intro x hx
      exfalso
      apply hS
      refine ⟨|x|, ?_⟩
      change 0 ≤ |x| ∧ t < f |x|
      refine ⟨abs_nonneg x, ?_⟩
      rw [habs]
      exact hx
end CohnElkies
