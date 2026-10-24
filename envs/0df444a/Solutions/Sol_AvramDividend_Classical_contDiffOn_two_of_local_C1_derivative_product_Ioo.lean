-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_two_of_local_C1_derivative_product_Ioo
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:08:46.933392+00:00
-- url     : https://prove2.me/submissions/1edb565c-3b98-4f3d-afbe-f4d516798c32

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- A local C1 logarithmic derivative in a product equation yields local C2. -/
theorem solution
    (W g : ℝ → ℝ) (a b : ℝ)
    (hW : ContinuousOn W (Ioo a b))
    (hg : ContDiffOn ℝ 1 g (Ioo a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt W (W x * g x) x) :
    ContDiffOn ℝ 2 W (Ioo a b) := by
  let s : Set ℝ := Ioo a b
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
        (isOpen_Ioo : IsOpen s)).2 ⟨hdiff, by simp, hzero⟩
    simpa using hraw
  have hderivfirst : ContDiffOn ℝ 1 (deriv W) s :=
    (hfirst.mul hg).congr heq
  have hraw : ContDiffOn ℝ (1 + 1) W s :=
    (contDiffOn_succ_iff_deriv_of_isOpen (n := 1)
      (isOpen_Ioo : IsOpen s)).2 ⟨hdiff, by simp, hderivfirst⟩
  have horder : ((1 : WithTop ENat) + 1) = 2 := by decide
  simpa only [horder] using hraw
