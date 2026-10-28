-- Prove2me | solution 1 for D1Bound5.smallPairTable_1_2_graph_property_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:31:45.143047+00:00
-- url     : https://prove2.me/submissions/18dc2152-d17f-4066-9c97-6fad76b0d4bf

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
import Definitions.Def_D1Bound5_SmallPairGraphData38_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphData41_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs33_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs34_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs35_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs36_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs37_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs39_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs40_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallTripleData_Definitions
import Theorems.Thm_D1Bound5_smallPairGraphProperty_of_orbit
import Theorems.Thm_D1Bound5_smallPairRepresentative_33_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_34_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_35_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_36_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_37_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_38_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_39_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_40_graph_property
import Theorems.Thm_D1Bound5_smallPairRepresentative_41_graph_property
import Theorems.Thm_D1Bound5_smallPairTable_1_2_orbits

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
    (e : QuadInt 1 2 ≃+* 𝓞 K)
    (row : Finset (ℤ × ℤ)) (hrow : row ∈ smallPairTable 1 2) :
    SmallPairGraphProperty (smallCoordinateSet 1 2 row) := by
  apply smallPairProperty_of_table_orbits smallPairs_1_2
    smallPairRepresentatives_1_2 smallPairTable_1_2_orbits ?_ row
    (by simpa [smallPairTable] using hrow)
  intro rep hrep
  simp only [smallPairRepresentatives_1_2, Finset.mem_insert, Finset.mem_singleton] at hrep
  rcases hrep with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have heq : smallCoordinateSet 1 2 {(-2,-1),(-3,1)} =
        {smallPairA_33,smallPairB_33} := by decide
    rw [heq]
    exact smallPairRepresentative_33_graph_property hK phi e
  · have heq : smallCoordinateSet 1 2 {(-2,-1),(0,-1)} =
        {smallPairA_34,smallPairB_34} := by decide
    rw [heq]
    exact smallPairRepresentative_34_graph_property hK phi e
  · have heq : smallCoordinateSet 1 2 {(-2,-1),(-1,2)} =
        {smallPairA_35,smallPairB_35} := by decide
    rw [heq]
    exact smallPairRepresentative_35_graph_property hK phi e
  · have heq : smallCoordinateSet 1 2 {(-2,-1),(1,0)} =
        {smallPairA_36,smallPairB_36} := by decide
    rw [heq]
    exact smallPairRepresentative_36_graph_property hK phi e
  · have heq : smallCoordinateSet 1 2 {(-2,-1),(3,-1)} =
        {smallPairA_37,smallPairB_37} := by decide
    rw [heq]
    exact smallPairRepresentative_37_graph_property hK phi e
  · have heq : smallCoordinateSet 1 2 {(-1,-1),(1,-1)} =
        {smallPairA_38,smallPairB_38} := by decide
    rw [heq]
    exact smallPairRepresentative_38_graph_property hK phi e
  · have heq : smallCoordinateSet 1 2 {(-1,-1),(1,1)} =
        {smallPairA_39,smallPairB_39} := by decide
    rw [heq]
    exact smallPairRepresentative_39_graph_property hK phi e
  · have heq : smallCoordinateSet 1 2 {(0,-2),(-2,2)} =
        {smallPairA_40,smallPairB_40} := by decide
    rw [heq]
    exact smallPairRepresentative_40_graph_property hK phi e
  · have heq : smallCoordinateSet 1 2 {(0,-2),(2,-2)} =
        {smallPairA_41,smallPairB_41} := by decide
    rw [heq]
    exact smallPairRepresentative_41_graph_property hK phi e













end D1Bound5
end
