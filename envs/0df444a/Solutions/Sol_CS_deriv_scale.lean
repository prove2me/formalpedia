-- Prove2me | solution 1 for CS.deriv_scale
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T21:51:24.630608+00:00
-- url     : https://prove2.me/submissions/64e1457c-64d5-445d-90cc-a820c09d553e

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
set_option autoImplicit true
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
open CS
variable {f : CS n E} {R x v : ℝ}

theorem solution {f : CS (n + 1) E} : (f.scale R).deriv = R⁻¹ • f.deriv.scale R := by
  have hasDerivAt_f (f : CS (n + 1) E) (x : ℝ) : HasDerivAt f (f.deriv x) x :=
    (f.h1.differentiable (by simp)).differentiableAt.hasDerivAt
  ext v
  by_cases hR : R = 0
  · simp [hR, CS.scale, CS.deriv]
  · simp only [CS.scale, hR, ↓reduceDIte, CS.smul_apply]
    exact ((hasDerivAt_f f (R⁻¹ • v)).scomp v
      (by simpa using! (hasDerivAt_id v).const_smul R⁻¹)).deriv
