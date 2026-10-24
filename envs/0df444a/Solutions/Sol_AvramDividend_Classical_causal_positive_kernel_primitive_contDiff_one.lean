-- Prove2me | solution 1 for AvramDividend.Classical.causal_positive_kernel_primitive_contDiff_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:56:19.28819+00:00
-- url     : https://prove2.me/submissions/8d8589e2-d4c3-4b88-90a8-6de60523c395

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped Topology

/-- A locally integrable causal kernel continuous at positive times has a C1 primitive. -/
theorem solution
    (K : ℝ → ℝ)
    (hK : ContinuousOn K (Ioi (0 : ℝ)))
    (hlocal : ∀ x : ℝ, 0 < x → IntervalIntegrable K volume 0 x) :
    ContDiffOn ℝ 1 (fun x : ℝ => ∫ s in (0 : ℝ)..x, K s) (Ioi 0) := by
  let F : ℝ → ℝ := fun x => ∫ s in (0 : ℝ)..x, K s
  let s : Set ℝ := Ioi (0 : ℝ)
  have hcont : ∀ x ∈ s, ContinuousAt K x := by
    intro x hx
    exact hK.continuousAt (isOpen_Ioi.mem_nhds hx)
  have hmeas : ∀ x ∈ s, StronglyMeasurableAtFilter K (𝓝 x) volume :=
    ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi hcont
  have hderiv : ∀ x ∈ s, HasDerivAt F (K x) x := by
    intro x hx
    exact intervalIntegral.integral_hasDerivAt_right
      (hlocal x hx) (hmeas x hx) (hcont x hx)
  have hdiff : DifferentiableOn ℝ F s := by
    intro x hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  have heq : EqOn (deriv F) K s := by
    intro x hx
    exact (hderiv x hx).deriv
  have hzero : ContDiffOn ℝ 0 (deriv F) s := by
    rw [contDiffOn_zero]
    exact hK.congr heq
  have hraw : ContDiffOn ℝ (0 + 1) F s :=
    (contDiffOn_succ_iff_deriv_of_isOpen (n := 0)
      (isOpen_Ioi : IsOpen s)).2 ⟨hdiff, by simp, hzero⟩
  simpa [F, s] using hraw
