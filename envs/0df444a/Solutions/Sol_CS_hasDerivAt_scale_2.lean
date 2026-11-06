-- Prove2me | solution 2 for CS.hasDerivAt_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:45:58.099205+00:00
-- url     : https://prove2.me/submissions/a9860580-7e81-431e-a24f-fd5d29d14497

import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
import Theorems.Thm_CS_hasDerivAt
import Theorems.Thm_P2M_CS_deriv_scale__14a24bbc31eb

set_option autoImplicit true
open Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap  BigOperators
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
open CS
variable {f : CS n E} {R x v : ℝ}
namespace CS
theorem _root_.solution (f : CS (n + 1) E) (R x : ℝ) :
    HasDerivAt (f.scale R) (R⁻¹ • _root_.deriv f (R⁻¹ • x)) x := by
  convert hasDerivAt (f.scale R) x ; rw [deriv_scale'] ; rfl
end CS
