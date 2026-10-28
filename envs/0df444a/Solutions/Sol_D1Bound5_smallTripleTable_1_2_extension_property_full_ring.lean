-- Prove2me | solution 1 for D1Bound5.smallTripleTable_1_2_extension_property_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:47:32.12872+00:00
-- url     : https://prove2.me/submissions/1bd7ee9c-a448-45ba-9d61-97aaa5d125d9

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
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallTripleData_Definitions
import Definitions.Def_D1Bound5_SmallTripleExtensionData10_Definitions
import Definitions.Def_D1Bound5_SmallTripleExtensionData9_Definitions
import Theorems.Thm_D1Bound5_smallTripleExtensionProperty_of_orbit
import Theorems.Thm_D1Bound5_smallTripleRepresentative_10_property
import Theorems.Thm_D1Bound5_smallTripleRepresentative_9_property
import Theorems.Thm_D1Bound5_smallTripleTable_orbits

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

private theorem smallTripleProperty_of_table_orbits {tau nu : ℤ}
    (table : List (Finset (ℤ × ℤ))) (reps : Finset (Finset (ℤ × ℤ)))
    (horbits : table.toFinset = reps.biUnion (smallTripleOrbit tau))
    (hreps : ∀ row ∈ reps, SmallTripleExtensionProperty (smallCoordinateSet tau nu row))
    (row : Finset (ℤ × ℤ)) (hrow : row ∈ table) :
    SmallTripleExtensionProperty (smallCoordinateSet tau nu row) := by
  have h : row ∈ reps.biUnion (smallTripleOrbit tau) := by
    rw [← horbits]
    exact List.mem_toFinset.mpr hrow
  obtain ⟨rep, hrep, horbit⟩ := Finset.mem_biUnion.mp h
  exact smallTripleExtensionProperty_of_orbit rep row (hreps rep hrep) horbit







theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (e : QuadInt 1 2 ≃+* 𝓞 K)
    (row : Finset (ℤ × ℤ)) (hrow : row ∈ smallTripleTable 1 2) :
    SmallTripleExtensionProperty (smallCoordinateSet 1 2 row) := by
  apply smallTripleProperty_of_table_orbits smallTriples_1_2
    smallTripleRepresentatives_1_2 smallTripleTable_orbits.2.2.2 ?_ row
    (by simpa [smallTripleTable] using hrow)
  intro rep hrep
  simp only [smallTripleRepresentatives_1_2, Finset.mem_insert, Finset.mem_singleton] at hrep
  rcases hrep with rfl | rfl
  · have heq : smallCoordinateSet 1 2 {(-2,-1),(-3,1),(1,0)} =
        {smallTripleAnchorA_9, smallTripleAnchorB_9, smallTripleAnchorC_9} := by decide
    rw [heq]
    exact smallTripleRepresentative_9_property hK phi e
  · have heq : smallCoordinateSet 1 2 {(-2,-1),(-1,2),(3,-1)} =
        {smallTripleAnchorA_10, smallTripleAnchorB_10, smallTripleAnchorC_10} := by decide
    rw [heq]
    exact smallTripleRepresentative_10_property hK phi e



end D1Bound5
end
