-- Prove2me | solution 1 for CS.tendsto_scale
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:25:23.829602+00:00
-- url     : https://prove2.me/submissions/12f429e4-550c-4c2b-97a3-bdf947e70c65

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

theorem solution (f : CS n E) (x : ℝ) : Tendsto (fun R => f.scale R x) atTop (𝓝 (f 0)) := by
  have h : Tendsto (fun R : ℝ => R⁻¹ • x) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.mul_const x
  apply (f.continuous.continuousAt.tendsto.comp h).congr'
  filter_upwards [eventually_ne_atTop 0] with R hR
  simp [scale, funscale, hR]
