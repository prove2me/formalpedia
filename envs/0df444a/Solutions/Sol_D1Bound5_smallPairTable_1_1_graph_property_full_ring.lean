-- Prove2me | solution 1 for D1Bound5.smallPairTable_1_1_graph_property_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:34:23.653974+00:00
-- url     : https://prove2.me/submissions/f689f05b-fac1-4a10-92e4-5c7c89a021ee

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
import Definitions.Def_D1Bound5_SmallPairGraphData18_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphData20_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs19_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs21_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs23_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs24_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs25_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs27_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs28_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs29_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs30_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallTripleData_Definitions
import Theorems.Thm_D1Bound5_smallPairGraphProperty_of_orbit
import Theorems.Thm_D1Bound5_smallPairRepresentative_18_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_19_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_20_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_21_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_22_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_23_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_24_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_25_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_26_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_27_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_28_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_29_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_30_graph_property
import Theorems.Thm_D1Bound5_smallPairTable_1_1_orbits

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
    (e : QuadInt 1 1 ≃+* 𝓞 K)
    (row : Finset (ℤ × ℤ)) (hrow : row ∈ smallPairTable 1 1) :
    SmallPairGraphProperty (smallCoordinateSet 1 1 row) := by
  apply smallPairProperty_of_table_orbits smallPairs_1_1
    smallPairRepresentatives_1_1 smallPairTable_1_1_orbits ?_ row
    (by simpa [smallPairTable] using hrow)
  intro rep hrep
  simp only [smallPairRepresentatives_1_1, Finset.mem_insert, Finset.mem_singleton] at hrep
  rcases hrep with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have heq : smallCoordinateSet 1 1 {(-2,-1),(0,-1)} =
        {smallPairA_18,smallPairB_18} := by decide
    rw [heq]
    exact smallPairRepresentative_18_graph_property hK phi e
  · have heq : smallCoordinateSet 1 1 {(-2,-1),(1,1)} =
        {smallPairA_19,smallPairB_19} := by decide
    rw [heq]
    exact smallPairRepresentative_19_graph_property hK phi e
  · have heq : smallCoordinateSet 1 1 {(-1,-2),(1,-2)} =
        {smallPairA_20,smallPairB_20} := by decide
    rw [heq]
    exact smallPairRepresentative_20_graph_property hK phi e
  · have heq : smallCoordinateSet 1 1 {(-1,-2),(0,1)} =
        {smallPairA_21,smallPairB_21} := by decide
    rw [heq]
    exact smallPairRepresentative_21_graph_property hK phi e
  · have heq : smallCoordinateSet 1 1 {(-2,0),(2,0)} =
        {smallPairA_22,smallPairB_22} := by decide
    rw [heq]
    exact smallPairRepresentative_22_graph_property hK phi e
  · have heq : smallCoordinateSet 1 1 {(-1,-1),(-2,1)} =
        {smallPairA_23,smallPairB_23} := by decide
    rw [heq]
    exact smallPairRepresentative_23_graph_property hK phi e
  · have heq : smallCoordinateSet 1 1 {(-1,-1),(2,-3)} =
        {smallPairA_24,smallPairB_24} := by decide
    rw [heq]
    exact smallPairRepresentative_24_graph_property hK phi e
  · have heq : smallCoordinateSet 1 1 {(-1,-1),(1,-1)} =
        {smallPairA_25,smallPairB_25} := by decide
    rw [heq]
    exact smallPairRepresentative_25_graph_property hK phi e
  · have heq : smallCoordinateSet 1 1 {(-1,-1),(1,0)} =
        {smallPairA_26,smallPairB_26} := by decide
    rw [heq]
    exact smallPairRepresentative_26_graph_property hK phi e
  · have heq : smallCoordinateSet 1 1 {(0,-2),(2,-2)} =
        {smallPairA_27,smallPairB_27} := by decide
    rw [heq]
    exact smallPairRepresentative_27_graph_property hK phi e
  · have heq : smallCoordinateSet 1 1 {(-1,0),(1,-3)} =
        {smallPairA_28,smallPairB_28} := by decide
    rw [heq]
    exact smallPairRepresentative_28_graph_property hK phi e
  · have heq : smallCoordinateSet 1 1 {(0,-1),(1,-2)} =
        {smallPairA_29,smallPairB_29} := by decide
    rw [heq]
    exact smallPairRepresentative_29_graph_property hK phi e
  · have heq : smallCoordinateSet 1 1 {(1,-2),(-1,2)} =
        {smallPairA_30,smallPairB_30} := by decide
    rw [heq]
    exact smallPairRepresentative_30_graph_property hK phi e















end D1Bound5
end
