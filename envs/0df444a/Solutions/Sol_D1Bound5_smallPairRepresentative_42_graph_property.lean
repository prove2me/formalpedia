-- Prove2me | solution 1 for D1Bound5.smallPairRepresentative_42_graph_property
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:44:27.469392+00:00
-- url     : https://prove2.me/submissions/6c8f1a17-9df9-4d11-91c4-c6be1bce91ad

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
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphData42_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphSymmetry_Definitions
import Theorems.Thm_D1Bound5_smallPairGraph_42_excludes_three_full_ring

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt



















































































/-- The full triangle exclusion for manuscript representative 42. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 3 ≃+* 𝓞 K) :
    SmallPairGraphProperty {smallPairA_42,smallPairB_42} := by
  intro t ht hproper hlarge hbound
  refine smallPairGraph_42_excludes_three_full_ring hK phi e t ht ?_ hlarge hbound ?_ ?_
  · intro j
    exact ⟨(hproper j).2.2 _ (by simp), (hproper j).2.2 _ (by simp)⟩
  · intro j h
    exact (hproper j).2.1 (by simp [h])
  · intro j h
    exact (hproper j).2.1 (by simp [h])













end D1Bound5
end
