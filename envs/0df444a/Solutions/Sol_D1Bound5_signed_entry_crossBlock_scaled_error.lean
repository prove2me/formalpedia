-- Prove2me | solution 1 for D1Bound5.signed_entry_crossBlock_scaled_error
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:01:15.265866+00:00
-- url     : https://prove2.me/submissions/eb8950b5-45dc-4e70-8d95-b20df36226b5

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_RootMatrixSigns_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg

section
open scoped BigOperators NumberField
open Module

namespace D1Bound5







/-- A selected signed root has an absolutely bounded second scaled error.
This is a finite algebraic consequence of the existing root perturbation
lemma, with no analytic square-root branch. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a b r : R) (u v : ℂ)
    (hu : u^2 = f a) (hv : v^2 = f b) (hr : r^2 = a*b+1)
    (hgood : SignedEntryGood f a b u v r) :
    ‖(f a*f b)*(u*f r*v)-(f a*f b)^2-(1/2 : ℂ)*(f a*f b)‖ <
      (2/15 : ℝ) := by
  have hrC : (f r)^2 = f a*f b+1 := by
    simpa only [map_pow, map_mul, map_add, map_one] using congrArg f hr
  have hsq : (u*f r*v)^2 = (f a*f b)*(f a*f b+1) := by
    rw [mul_pow, mul_pow, hu, hv, hrC]
    ring
  have hid : (f a*f b)*(u*f r*v)-(f a*f b)^2-(1/2 : ℂ)*(f a*f b) =
      -(u*f r*v-f a*f b)^2/2 := by
    linear_combination (1/2 : ℂ)*hsq
  have hnear : ‖u*f r*v-f a*f b‖ < (16/31 : ℝ) := hgood.1
  have hsquare : ‖u*f r*v-f a*f b‖^2 < (16/31 : ℝ)^2 := by
    nlinarith [norm_nonneg (u*f r*v-f a*f b)]
  rw [hid, norm_div, norm_neg, norm_pow, Complex.norm_two]
  nlinarith only [hsquare]



end D1Bound5
end
