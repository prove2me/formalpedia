-- Prove2me | solution 1 for D1Bound5.smallTriple_classified_normalized
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:44:36.379663+00:00
-- url     : https://prove2.me/submissions/01701cb6-2340-477b-83a2-5255564270df

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
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
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallTripleCheck_Definitions
import Definitions.Def_D1Bound5_SmallTripleData_Definitions
import Theorems.Thm_D1Bound5_noSmallTriple_of_large_discriminant
import Theorems.Thm_D1Bound5_smallTriple_classified_rectangular

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt



/-- Complete classification over every positive normalized coordinate model. -/
theorem _root_.solution {tau nu : ℤ}
    (htau : tau = 0 ∨ tau = 1) (hpos : 0 < discriminant tau nu)
    (t : Fin 3 → QuadInt tau nu) (ht : IsD1Tuple t)
    (hnorm : ∀ i, (t i).norm ≤ 8) :
    tripleCoordinates (t 0) (t 1) (t 2) ∈ smallTripleTable tau nu := by
  by_cases hcut : discriminant tau nu ≤ 32
  · have hnu : 1 ≤ nu ∧ nu ≤ 8 := by
      rcases htau with rfl | rfl
      · simp only [discriminant, zero_pow (by decide : 2 ≠ 0), sub_zero] at hpos hcut
        omega
      · simp only [discriminant, one_pow] at hpos hcut
        omega
    exact smallTriple_classified_rectangular htau hnu.1 hnu.2 t ht hnorm
  · exact (noSmallTriple_of_large_discriminant (lt_of_not_ge hcut) t ht hnorm).elim



end D1Bound5
end
