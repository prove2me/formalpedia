-- Prove2me | solution 1 for D1Bound5.smallTripleTable_extension_property_full_ring
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:36:17.632473+00:00
-- url     : https://prove2.me/submissions/86062f07-4db6-49a1-9bf8-a0f93cb8c83e

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
import Theorems.Thm_D1Bound5_smallTripleTable_0_1_extension_property_full_ring
import Theorems.Thm_D1Bound5_smallTripleTable_0_2_extension_property_full_ring
import Theorems.Thm_D1Bound5_smallTripleTable_1_1_extension_property_full_ring
import Theorems.Thm_D1Bound5_smallTripleTable_1_2_extension_property_full_ring

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt











/-- All 24 coordinate triples inherit the representative extension theorem;
no ordering or unproved symmetry convention is imposed on the input row. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    {tau nu : ℤ} (e : QuadInt tau nu ≃+* 𝓞 K)
    (hmodel : (tau = 0 ∧ nu = 1) ∨ (tau = 0 ∧ nu = 2) ∨
      (tau = 1 ∧ nu = 1) ∨ (tau = 1 ∧ nu = 2))
    (row : Finset (ℤ × ℤ)) (hrow : row ∈ smallTripleTable tau nu) :
    SmallTripleExtensionProperty (smallCoordinateSet tau nu row) := by
  rcases hmodel with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact smallTripleTable_0_1_extension_property_full_ring hK phi e row hrow
  · exact smallTripleTable_0_2_extension_property_full_ring hK phi e row hrow
  · exact smallTripleTable_1_1_extension_property_full_ring hK phi e row hrow
  · exact smallTripleTable_1_2_extension_property_full_ring hK phi e row hrow

end D1Bound5
end
