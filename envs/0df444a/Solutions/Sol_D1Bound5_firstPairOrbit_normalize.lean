-- Prove2me | solution 1 for D1Bound5.firstPairOrbit_normalize
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:19:15.742032+00:00
-- url     : https://prove2.me/submissions/a19848ca-3bea-456b-859b-6b5a37417259

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
import Definitions.Def_D1Bound5_FirstPairData_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_OneSmallSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Theorems.Thm_D1Bound5_firstPairCoordinates_eq
import Theorems.Thm_D1Bound5_smallExtensionSymmetry_involutive

section
namespace D1Bound5
open QuadInt







/-- The ordered coordinate orbit admits actual involutive normalization. -/
theorem _root_.solution {tau nu : ℤ}
    (a b : QuadInt tau nu) (row : (ℤ × ℤ) × (ℤ × ℤ))
    (horbit : firstPairCoordinates a b ∈ firstPairOrbit tau row) :
    ∃ sgn conj : Bool,
      smallExtensionSymmetry sgn conj a = firstPairRowA tau nu row ∧
      smallExtensionSymmetry sgn conj b = firstPairRowB tau nu row := by
  have hdecode (sgn conj : Bool)
      (h : firstPairCoordinates a b = firstPairCoordinates
        (smallExtensionSymmetry sgn conj (firstPairRowA tau nu row))
        (smallExtensionSymmetry sgn conj (firstPairRowB tau nu row))) :
      smallExtensionSymmetry sgn conj a = firstPairRowA tau nu row ∧
      smallExtensionSymmetry sgn conj b = firstPairRowB tau nu row := by
    obtain ⟨ha,hb⟩ := firstPairCoordinates_eq _ _ _ _ h
    constructor
    · rw [ha]
      exact smallExtensionSymmetry_involutive sgn conj _
    · rw [hb]
      exact smallExtensionSymmetry_involutive sgn conj _
  simp only [firstPairOrbit, Finset.mem_insert, Finset.mem_singleton] at horbit
  rcases horbit with h | h | h | h
  · refine ⟨false,false,hdecode false false ?_⟩
    simpa [firstPairCoordinates,firstPairRowA,firstPairRowB,smallExtensionSymmetry] using h
  · refine ⟨true,false,hdecode true false ?_⟩
    simpa [firstPairCoordinates,firstPairRowA,firstPairRowB,smallExtensionSymmetry] using h
  · refine ⟨false,true,hdecode false true ?_⟩
    simpa [firstPairCoordinates,firstPairRowA,firstPairRowB,smallExtensionSymmetry] using h
  · refine ⟨true,true,hdecode true true ?_⟩
    simpa [firstPairCoordinates,firstPairRowA,firstPairRowB,smallExtensionSymmetry,
      neg_add_rev, sub_eq_add_neg, add_comm] using h







end D1Bound5
end
