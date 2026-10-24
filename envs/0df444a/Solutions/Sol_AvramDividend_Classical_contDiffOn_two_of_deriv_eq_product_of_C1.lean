-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_two_of_deriv_eq_product_of_C1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:21:43.92705+00:00
-- url     : https://prove2.me/submissions/5a4260c2-f9ad-4207-9841-fbccb17128d0

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- A C¹ coefficient in the derivative product equation makes the solution C². -/
theorem solution
    (W g : ℝ → ℝ)
    (hW : ContinuousOn W (Ioi (0 : ℝ)))
    (hg : ContDiffOn ℝ 1 g (Ioi (0 : ℝ)))
    (hderiv : ∀ x : ℝ, 0 < x → HasDerivAt W (W x * g x) x) :
    ContDiffOn ℝ 2 W (Ioi (0 : ℝ)) := by
  let s : Set ℝ := Ioi (0 : ℝ)
  have hdiff : DifferentiableOn ℝ W s := by
    intro x hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  have heq : EqOn (deriv W) (fun x => W x * g x) s := by
    intro x hx
    exact (hderiv x hx).deriv
  have hfirst : ContDiffOn ℝ 1 W s := by
    have hzero : ContDiffOn ℝ 0 (deriv W) s := by
      rw [contDiffOn_zero]
      exact (hW.mul hg.continuousOn).congr heq
    have hraw : ContDiffOn ℝ (0 + 1) W s :=
      (contDiffOn_succ_iff_deriv_of_isOpen (n := 0)
        (isOpen_Ioi : IsOpen s)).2 ⟨hdiff, by simp, hzero⟩
    simpa using hraw
  have hderivfirst : ContDiffOn ℝ 1 (deriv W) s :=
    (hfirst.mul hg).congr heq
  have hraw : ContDiffOn ℝ (1 + 1) W s :=
    (contDiffOn_succ_iff_deriv_of_isOpen (n := 1)
      (isOpen_Ioi : IsOpen s)).2 ⟨hdiff, by simp, hderivfirst⟩
  have horder : ((1 : WithTop ENat) + 1) = 2 := by decide
  simpa only [horder] using hraw
