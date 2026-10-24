-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_two_of_deriv_eq_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:27:16.378052+00:00
-- url     : https://prove2.me/submissions/b1bf048b-aab9-4060-8edc-c66857640c18

import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    (f g : ℝ → ℝ)
    (hfdiff : DifferentiableOn ℝ f (Ioi (0 : ℝ)))
    (hg : ContDiffOn ℝ 1 g (Ioi (0 : ℝ)))
    (hderiv : ∀ x : ℝ, 0 < x → deriv f x = g x) :
    ContDiffOn ℝ 2 f (Ioi (0 : ℝ)) := by
  have hder : ContDiffOn ℝ 1 (deriv f) (Ioi (0 : ℝ)) := by
    apply hg.congr
    intro x hx
    exact hderiv x hx
  have h : ContDiffOn ℝ (1 + 1) f (Ioi (0 : ℝ)) :=
    (contDiffOn_succ_iff_deriv_of_isOpen
        (n := 1) (f := f) (s := Ioi (0 : ℝ)) isOpen_Ioi).2
      ⟨hfdiff, by simp, hder⟩
  simpa only [one_add_one_eq_two] using h
