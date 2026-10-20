-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_one_of_deriv_eq_continuous_product_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:32:59.402677+00:00
-- url     : https://prove2.me/submissions/d4bb7d50-4064-4d8f-a8dd-e43aa0a2fa5c

import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    (W g : ℝ → ℝ)
    (hg : ContinuousOn g (Ioi 0))
    (hderiv : ∀ x : ℝ, 0 < x → HasDerivAt W (g x * W x) x) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  have hdiff : DifferentiableOn ℝ W (Ioi (0 : ℝ)) := by
    intro x hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  have hWcont : ContinuousOn W (Ioi (0 : ℝ)) := hdiff.continuousOn
  have hprod : ContinuousOn (fun x : ℝ => g x * W x) (Ioi 0) :=
    hg.mul hWcont
  have hderivCont : ContinuousOn (deriv W) (Ioi (0 : ℝ)) := by
    apply hprod.congr
    intro x hx
    exact (hderiv x hx).deriv
  apply (contDiffOn_succ_iff_deriv_of_isOpen
    (n := 0) (f := W) (s := Ioi (0 : ℝ)) isOpen_Ioi).2
  exact ⟨hdiff, by simp, contDiffOn_zero.mpr hderivCont⟩
