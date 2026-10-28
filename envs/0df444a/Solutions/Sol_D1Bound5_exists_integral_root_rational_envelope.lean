-- Prove2me | solution 1 for D1Bound5.exists_integral_root_rational_envelope
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:21:56.403172+00:00
-- url     : https://prove2.me/submissions/d87bf323-ab8e-4767-a0ff-cc78c68b3b2e

import Lean.Util.CollectAxioms
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Theorems.Thm_D1Bound5_exists_root_error_rational_envelope

section
namespace D1Bound5



/-- Select the sign inside the original ring while retaining its exact
square equation. The source root is allowed to be zero. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ) (a b r : R) (u v : ℂ)
    (hu : u^2 = f a) (hv : v^2 = f b) (hr : r^2 = a*b+1)
    (m c k : ℝ) (hm : 0 < m) (hc : 0 ≤ c) (hk : 1/2 < k)
    (hgap : 1 < (1-c^2)*m) (hprecision : 1 ≤ 2*m*(1+c)^2*(k-1/2))
    (hab : m ≤ ‖f a*f b‖) :
    ∃ q : R, q^2 = a*b+1 ∧ ‖u*f q*v-f a*f b-(1/2 : ℂ)‖ ≤ k-1/2 := by
  have hrC : (f r)^2 = f a*f b+1 := by
    simpa only [map_pow,map_mul,map_add,map_one] using congrArg f hr
  have ht : (u*f r*v)^2 = (f a*f b)*(f a*f b+1) := by
    rw [mul_pow,mul_pow,hu,hv,hrC]
    ring
  obtain ⟨t,htsign,hbound⟩ := exists_root_error_rational_envelope
    (f a*f b) (u*f r*v) m c k hm hc hk hgap hprecision hab ht
  rcases htsign with rfl | rfl
  · exact ⟨r,hr,hbound⟩
  · refine ⟨-r,by simpa only [neg_sq] using hr,?_⟩
    simpa only [map_neg,mul_neg,neg_mul] using hbound







end D1Bound5
end
