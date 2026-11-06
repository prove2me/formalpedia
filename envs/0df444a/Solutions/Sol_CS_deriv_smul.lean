-- Prove2me | solution 1 for CS.deriv_smul
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:24:12.255932+00:00
-- url     : https://prove2.me/submissions/cb086422-d68a-448b-81be-6eccba211b52

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
theorem solution {f : CS (n + 1) E} : (R • f).deriv = R • f.deriv := by
  apply CS.ext
  funext x
  exact deriv_const_smul_field R f.toFun
