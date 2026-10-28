-- Prove2me | solution 1 for D1Bound5.oneSmallRowMembership_full_ring_excludes_irregular_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:25:02.264563+00:00
-- url     : https://prove2.me/submissions/9f46bc88-76bc-4e4f-9496-762649fc2804

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Theorems.Thm_D1Bound5_oneSmallRowMembership_full_ring_bound

section
open scoped NumberField Classical
open Module

namespace D1Bound5
open QuadInt





/-- The finite complement contradicts the strict tail-growth lower bound
in every one of the 56 rows, including the two formerly exceptional rows. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    {tau nu : ℤ} (e : QuadInt tau nu ≃+* 𝓞 K) (phi : K →+* ℂ)
    (sgn conj : Bool) (a b s z : 𝓞 K) (cutoff : ℤ)
    (hrow : OneSmallRowMembership
      (smallExtensionSymmetry sgn conj (e.symm a))
      (smallExtensionSymmetry sgn conj (e.symm b))
      (smallExtensionSymmetry sgn conj (e.symm s)) cutoff)
    (hz : ‖phi (z : K)‖^2 < (cutoff : ℝ))
    (ha : ∃ q : 𝓞 K, q*q = a*z+1) (hb : ∃ q : 𝓞 K, q*q = b*z+1)
    (hs : ∃ q : 𝓞 K, q*q = s*z+1)
    (hgrowth : 4*‖phi (b : K)‖^2*‖phi (s : K)‖^2 < ‖phi (z : K)‖^2) : False := by
  exact (not_le_of_gt hgrowth)
    (oneSmallRowMembership_full_ring_bound e phi sgn conj a b s z cutoff hrow hz ha hb hs)

end D1Bound5
end
