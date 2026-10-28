-- Prove2me | solution 1 for D1Bound5.smallPairTable_graph_property_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:19:01.979983+00:00
-- url     : https://prove2.me/submissions/d634e01d-1cc9-4229-b5ca-7f3dbdb5fe3a

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
import Definitions.Def_D1Bound5_SmallPairClassification_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphSymmetry_Definitions
import Theorems.Thm_D1Bound5_smallPairTable_0_1_graph_property_full_ring
import Theorems.Thm_D1Bound5_smallPairTable_0_2_graph_property_full_ring
import Theorems.Thm_D1Bound5_smallPairTable_0_5_graph_property_full_ring
import Theorems.Thm_D1Bound5_smallPairTable_0_6_graph_property_full_ring
import Theorems.Thm_D1Bound5_smallPairTable_1_1_graph_property_full_ring
import Theorems.Thm_D1Bound5_smallPairTable_1_2_graph_property_full_ring
import Theorems.Thm_D1Bound5_smallPairTable_1_3_graph_property_full_ring
import Theorems.Thm_D1Bound5_smallPairTable_1_4_graph_property_full_ring
import Theorems.Thm_D1Bound5_smallPairTable_1_5_graph_property_full_ring
import Theorems.Thm_D1Bound5_smallPairTable_1_6_graph_property_full_ring
import Theorems.Thm_D1Bound5_smallPairTable_1_8_graph_property_full_ring

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt

























/-- Every table row inherits its representative triangle exclusion. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {tau nu : ℤ} (e : QuadInt tau nu ≃+* 𝓞 K)
    (hmodel : (tau,nu) ∈ smallPairModels)
    (row : Finset (ℤ × ℤ)) (hrow : row ∈ smallPairTable tau nu) :
    SmallPairGraphProperty (smallCoordinateSet tau nu row) := by
  simp only [smallPairModels, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hmodel
  rcases hmodel with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact smallPairTable_0_1_graph_property_full_ring hK phi e row hrow
  · exact smallPairTable_0_2_graph_property_full_ring hK phi e row hrow
  · exact smallPairTable_0_5_graph_property_full_ring hK phi e row hrow
  · exact smallPairTable_0_6_graph_property_full_ring hK phi e row hrow
  · exact smallPairTable_1_1_graph_property_full_ring hK phi e row hrow
  · exact smallPairTable_1_2_graph_property_full_ring hK phi e row hrow
  · exact smallPairTable_1_3_graph_property_full_ring hK phi e row hrow
  · exact smallPairTable_1_4_graph_property_full_ring hK phi e row hrow
  · exact smallPairTable_1_5_graph_property_full_ring hK phi e row hrow
  · exact smallPairTable_1_6_graph_property_full_ring hK phi e row hrow
  · exact smallPairTable_1_8_graph_property_full_ring hK phi e row hrow

end D1Bound5
end
