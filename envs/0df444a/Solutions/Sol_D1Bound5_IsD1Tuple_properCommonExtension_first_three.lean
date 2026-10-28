-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.properCommonExtension_first_three
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:35:36.770196+00:00
-- url     : https://prove2.me/submissions/9212511e-4ab5-41a4-a1da-85f25cf6553e

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
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions

section
open scoped NumberField Classical
open Module

namespace D1Bound5



/-- Every entry after the first three is a proper common extension of them.
The statement does not impose any condition on mutation intermediates. -/
theorem _root_.solution
    {R : Type*} [CommRing R] [DecidableEq R]
    (t : Fin 6 → R) (ht : IsD1Tuple t) (j : Fin 6) (hj : 3 ≤ j) :
    ProperCommonExtension {t 0,t 1,t 2} (t j) := by
  refine ⟨ht.2.1 j, ?_, ?_⟩
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · have := ht.1 h
      omega
    · have := ht.1 h
      omega
    · have := ht.1 h
      omega
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact ht.2.2 0 j (by omega)
    · exact ht.2.2 1 j (by omega)
    · exact ht.2.2 2 j (by omega)



end D1Bound5
end
