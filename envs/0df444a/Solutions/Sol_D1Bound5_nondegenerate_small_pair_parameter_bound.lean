-- Prove2me | solution 1 for D1Bound5.nondegenerate_small_pair_parameter_bound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:25:55.310644+00:00
-- url     : https://prove2.me/submissions/78234245-567d-4a89-9873-d6245a9d3cb5

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Theorems.Thm_D1Bound5_small_pair_of_large_discriminant

section
namespace D1Bound5
open QuadInt









/-- Every nondegenerate compatible small pair belongs to a finite rectangle
of normalized coordinate parameters. -/
theorem _root_.solution {tau nu : ℤ}
    (htau : tau = 0 ∨ tau = 1) (hd : 0 < discriminant tau nu)
    (a b : QuadInt tau nu) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hNa : a.norm ≤ 8) (hNb : b.norm ≤ 8)
    (hsquare : ∃ r, r*r = a*b+1) (hnondeg : a*b+1 ≠ 0) :
    discriminant tau nu ≤ 32 ∧ 1 ≤ nu ∧ nu ≤ 8 := by
  have hcut : discriminant tau nu ≤ 32 := by
    by_contra h
    rcases small_pair_of_large_discriminant (lt_of_not_ge h) a b ha hb hab
      hNa hNb hsquare with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals norm_num at hnondeg
  refine ⟨hcut, ?_⟩
  rcases htau with rfl | rfl
  · simp only [discriminant, zero_pow (by decide : 2 ≠ 0), sub_zero] at hd hcut
    omega
  · simp only [discriminant, one_pow] at hd hcut
    omega

end D1Bound5
end
