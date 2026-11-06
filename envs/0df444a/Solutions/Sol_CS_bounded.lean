-- Prove2me | solution 1 for CS.bounded
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:23:25.775268+00:00
-- url     : https://prove2.me/submissions/e20e694d-6d9a-4796-8709-e9bcf927507b

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

theorem solution : ∃ C, ∀ v, ‖f v‖ ≤ C := by
  exact f.continuous.bounded_above_of_compact_support f.h2
