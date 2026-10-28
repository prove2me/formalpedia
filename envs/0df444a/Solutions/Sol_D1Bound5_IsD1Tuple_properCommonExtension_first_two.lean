-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.properCommonExtension_first_two
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:59:15.248691+00:00
-- url     : https://prove2.me/submissions/d82366ed-9a7e-481c-9219-522c2f20ee2a

import Init
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Ring.Abs
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
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Range
import Mathlib.Data.ZMod.Basic
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
import Definitions.Def_D1Bound5_SmallPairPureClosureData10_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData14_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData15_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData21_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData23_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData28_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData30_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData36_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData4_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData6_Definitions
import Definitions.Def_D1Bound5_SmallPairPureClosureData8_Definitions

section
open scoped NumberField Classical
open Module

namespace D1Bound5

/-- All entries following the first two are proper common extensions. -/
theorem _root_.solution
    {R : Type*} [CommRing R] [DecidableEq R]
    (t : Fin 6 → R) (ht : IsD1Tuple t) (j : Fin 6) (hj : 2 ≤ j) :
    ProperCommonExtension {t 0,t 1} (t j) := by
  refine ⟨ht.2.1 j, ?_, ?_⟩
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h
    · have := ht.1 h
      omega
    · have := ht.1 h
      omega
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact ht.2.2 0 j (by omega)
    · exact ht.2.2 1 j (by omega)



end D1Bound5
end
