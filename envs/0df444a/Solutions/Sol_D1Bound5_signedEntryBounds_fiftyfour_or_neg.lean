-- Prove2me | solution 1 for D1Bound5.signedEntryBounds_fiftyfour_or_neg
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:49:47.957478+00:00
-- url     : https://prove2.me/submissions/5a00e542-5a61-4468-a10f-81d973e1ec9e

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
import Definitions.Def_D1Bound5_MixedRootMatrixSigns_Definitions
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg
import Theorems.Thm_D1Bound5_exists_root_error_control

section
namespace D1Bound5

/-- Uniform last-column estimate, including the endpoint |ab| = 54. -/
theorem _root_.solution
    {R : Type*} [CommRing R] (f : R →+* ℂ)
    (a b r : R) (u v : ℂ)
    (hu : u^2 = f a) (hv : v^2 = f b)
    (hr : r^2 = a*b+1) (hab : 54 ≤ ‖f a * f b‖) :
    SignedEntryBounds f a b u v r (50/99) (625/264627) ∨
      SignedEntryBounds f a b u v (-r) (50/99) (625/264627) := by
  let x := f a * f b
  have hx : 0 < ‖x‖ := by dsimp [x]; linarith
  have hg : 1 < (1-(49/50 : ℝ)^2)*‖x‖ := by
    dsimp [x]
    nlinarith only [hab]
  have ht : (u * f r * v)^2 = x*(x+1) := by
    have h := congrArg f hr
    simp only [map_pow, map_mul, map_add, map_one] at h
    rw [mul_pow, mul_pow, hu, hv, h]
    dsimp [x]
    ring
  obtain ⟨t, ht, hn, he⟩ := exists_root_error_control x (u*f r*v)
    (49/50) (by norm_num) hx hg ht
  have hn' : ‖t-x‖ < (50/99 : ℝ) := by nlinarith only [hn]
  have hm := mul_nonneg (sub_nonneg.mpr hab)
    (norm_nonneg ((t-x)-(1/2 : ℂ)))
  have he' : ‖(t-x)-(1/2 : ℂ)‖ < (625/264627 : ℝ) := by
    change 0 ≤ (‖x‖-54)*‖(t-x)-(1/2 : ℂ)‖ at hm
    nlinarith only [he, hm]
  rcases ht with ht | ht
  · left
    simpa only [SignedEntryBounds, ← ht, x] using And.intro hn' he'
  · right
    have hs : u*f (-r)*v = t := by rw [ht, map_neg]; ring
    simpa only [SignedEntryBounds, hs, x] using And.intro hn' he'















open scoped NumberField
open Module








end D1Bound5
end
