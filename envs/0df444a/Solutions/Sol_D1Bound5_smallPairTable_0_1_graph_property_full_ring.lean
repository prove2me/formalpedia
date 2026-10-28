-- Prove2me | solution 1 for D1Bound5.smallPairTable_0_1_graph_property_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:31:41.13899+00:00
-- url     : https://prove2.me/submissions/bfa4e66c-7da8-403c-949f-126674627e51

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
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallPairClassificationData_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphData2_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphData9_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs10_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs11_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs12_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs1_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs3_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs4_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs5_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs6_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs7_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs8_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallTripleData_Definitions
import Theorems.Thm_D1Bound5_smallPairGraphProperty_of_orbit
import Theorems.Thm_D1Bound5_smallPairRepresentative_10_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_11_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_12_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_1_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_2_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_3_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_4_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_5_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_6_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_7_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_8_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_9_graph_property
import Theorems.Thm_D1Bound5_smallPairTable_0_1_orbits

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

private theorem smallPairProperty_of_table_orbits {tau nu : ℤ}
    (table : List (Finset (ℤ × ℤ))) (reps : Finset (Finset (ℤ × ℤ)))
    (horbits : table.toFinset = reps.biUnion (smallTripleOrbit tau))
    (hreps : ∀ row ∈ reps, SmallPairGraphProperty (smallCoordinateSet tau nu row))
    (row : Finset (ℤ × ℤ)) (hrow : row ∈ table) :
    SmallPairGraphProperty (smallCoordinateSet tau nu row) := by
  have h : row ∈ reps.biUnion (smallTripleOrbit tau) := by
    rw [← horbits]
    exact List.mem_toFinset.mpr hrow
  obtain ⟨rep, hrep, horbit⟩ := Finset.mem_biUnion.mp h
  exact smallPairGraphProperty_of_orbit rep row (hreps rep hrep) horbit

theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 0 1 ≃+* 𝓞 K)
    (row : Finset (ℤ × ℤ)) (hrow : row ∈ smallPairTable 0 1) :
    SmallPairGraphProperty (smallCoordinateSet 0 1 row) := by
  apply smallPairProperty_of_table_orbits smallPairs_0_1
    smallPairRepresentatives_0_1 smallPairTable_0_1_orbits ?_ row
    (by simpa [smallPairTable] using hrow)
  intro rep hrep
  simp only [smallPairRepresentatives_0_1, Finset.mem_insert, Finset.mem_singleton] at hrep
  rcases hrep with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have heq : smallCoordinateSet 0 1 {(-2,-2),(-2,2)} =
        {smallPairA_1,smallPairB_1} := by decide
    rw [heq]
    exact smallPairRepresentative_1_graph_property hK phi e
  · have heq : smallCoordinateSet 0 1 {(-2,-2),(0,-2)} =
        {smallPairA_2,smallPairB_2} := by decide
    rw [heq]
    exact smallPairRepresentative_2_graph_property hK phi e
  · have heq : smallCoordinateSet 0 1 {(-2,-2),(2,0)} =
        {smallPairA_3,smallPairB_3} := by decide
    rw [heq]
    exact smallPairRepresentative_3_graph_property hK phi e
  · have heq : smallCoordinateSet 0 1 {(-2,-1),(0,-1)} =
        {smallPairA_4,smallPairB_4} := by decide
    rw [heq]
    exact smallPairRepresentative_4_graph_property hK phi e
  · have heq : smallCoordinateSet 0 1 {(-2,-1),(0,2)} =
        {smallPairA_5,smallPairB_5} := by decide
    rw [heq]
    exact smallPairRepresentative_5_graph_property hK phi e
  · have heq : smallCoordinateSet 0 1 {(-2,-1),(2,-1)} =
        {smallPairA_6,smallPairB_6} := by decide
    rw [heq]
    exact smallPairRepresentative_6_graph_property hK phi e
  · have heq : smallCoordinateSet 0 1 {(-2,0),(-1,-2)} =
        {smallPairA_7,smallPairB_7} := by decide
    rw [heq]
    exact smallPairRepresentative_7_graph_property hK phi e
  · have heq : smallCoordinateSet 0 1 {(-2,0),(1,0)} =
        {smallPairA_8,smallPairB_8} := by decide
    rw [heq]
    exact smallPairRepresentative_8_graph_property hK phi e
  · have heq : smallCoordinateSet 0 1 {(-1,-2),(1,-2)} =
        {smallPairA_9,smallPairB_9} := by decide
    rw [heq]
    exact smallPairRepresentative_9_graph_property hK phi e
  · have heq : smallCoordinateSet 0 1 {(-1,-2),(1,0)} =
        {smallPairA_10,smallPairB_10} := by decide
    rw [heq]
    exact smallPairRepresentative_10_graph_property hK phi e
  · have heq : smallCoordinateSet 0 1 {(-1,-1),(1,-1)} =
        {smallPairA_11,smallPairB_11} := by decide
    rw [heq]
    exact smallPairRepresentative_11_graph_property hK phi e
  · have heq : smallCoordinateSet 0 1 {(0,-2),(0,-1)} =
        {smallPairA_12,smallPairB_12} := by decide
    rw [heq]
    exact smallPairRepresentative_12_graph_property hK phi e























end D1Bound5
end
