-- Prove2me | solution 1 for CS.hasDerivAt_scale
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:28:32.35691+00:00
-- url     : https://prove2.me/submissions/410668cc-34d1-485c-a225-25b3ee5752db

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
set_option autoImplicit true
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
open CS
variable {f : CS n E} {R x v : ℝ}

theorem solution (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • _root_.deriv f (R⁻¹ • x)) x := by
  by_cases hR : R = 0
  · subst R
    simp [CS.scale]
  · have hf : HasDerivAt (f : ℝ → E) (_root_.deriv f (R⁻¹ • x)) (R⁻¹ • x) :=
      (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt
    have hg : HasDerivAt (fun y : ℝ => R⁻¹ • y) R⁻¹ x := by
      simpa [smul_eq_mul] using (hasDerivAt_id x).const_mul R⁻¹
    simpa only [CS.scale, dif_neg hR, funscale, Function.comp_def] using hf.scomp x hg
