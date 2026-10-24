-- Prove2me | solution 1 for AvramDividend.Classical.causal_damped_resolvent_C1_of_continuous_forcing
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T23:41:28.012118+00:00
-- url     : https://prove2.me/submissions/a37fb739-031a-4b8a-aa16-eb6529c6a1ae

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Order.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- A causal first-order damping equation with continuous forcing gives
C1 regularity once genuine pointwise derivatives are available. -/
theorem solution
    (H g : ℝ → ℝ) (w : ℝ)
    (hg : ContinuousOn g (Ioi (0 : ℝ)))
    (hderiv : ∀ x : ℝ, 0 < x →
      HasDerivAt H (g x - w * H x) x) :
    ContDiffOn ℝ 1 H (Ioi (0 : ℝ)) := by
  let s : Set ℝ := Ioi (0 : ℝ)
  have hdiff : DifferentiableOn ℝ H s := by
    intro x hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  have hHcont : ContinuousOn H s := hdiff.continuousOn
  have hrhs : ContinuousOn (fun x => g x - w * H x) s :=
    hg.sub (continuousOn_const.mul hHcont)
  have heq : EqOn (deriv H) (fun x => g x - w * H x) s := by
    intro x hx
    exact (hderiv x hx).deriv
  have hzero : ContDiffOn ℝ 0 (deriv H) s := by
    rw [contDiffOn_zero]
    exact hrhs.congr heq
  have hraw : ContDiffOn ℝ (0 + 1) H s :=
    (contDiffOn_succ_iff_deriv_of_isOpen (n := 0)
      (isOpen_Ioi : IsOpen s)).2 ⟨hdiff, by simp, hzero⟩
  simpa [s] using hraw
