-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.small_triple_bounded_extensions
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:12:19.787881+00:00
-- url     : https://prove2.me/submissions/136e99cc-8650-4f5b-99da-1ff90cda5cea

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
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallExtensionSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallTripleCheck_Definitions
import Definitions.Def_D1Bound5_SmallTripleData_Definitions
import Theorems.Thm_D1Bound5_IsD1Tuple_small_triple_classification
import Theorems.Thm_D1Bound5_SmallTripleExtensionProperty_full_ring
import Theorems.Thm_D1Bound5_smallTripleTable_extension_property_full_ring

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt























theorem smallCoordinateSet_triple {tau nu : ℤ} (a b c : QuadInt tau nu) :
    smallCoordinateSet tau nu (tripleCoordinates a b c) = {a,b,c} := by
  simp [smallCoordinateSet, tripleCoordinates]



end D1Bound5
end

section
open scoped NumberField Classical
open Module

namespace D1Bound5
open QuadInt



/-- Every actual small D(1)-triple has at most one distinct nonzero further
common extension in the radius-10^40 disk. Every such extension has modulus
strictly less than 85. The classification, symmetries, finite certificates
and reversible descent are all supplied by proved dependencies. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 3 → 𝓞 K) (ht : IsD1Tuple t)
    (hsmall : ∀ i, ‖phi (t i : K)‖ < 3) :
    (∀ z : 𝓞 K, ProperCommonExtension {t 0,t 1,t 2} z →
      ‖phi (z : K)‖^2 ≤ (10 : ℝ)^80 → ‖phi (z : K)‖ < 85) ∧
    (∀ z w : 𝓞 K, ProperCommonExtension {t 0,t 1,t 2} z →
      ProperCommonExtension {t 0,t 1,t 2} w →
      ‖phi (z : K)‖^2 ≤ (10 : ℝ)^80 →
      ‖phi (w : K)‖^2 ≤ (10 : ℝ)^80 → z = w) := by
  classical
  obtain ⟨tau, nu, e, hmodel, hrow⟩ :=
    IsD1Tuple.small_triple_classification hK phi t ht hsmall
  have hproperty := smallTripleTable_extension_property_full_ring hK phi e hmodel
    (tripleCoordinates (e.symm (t 0)) (e.symm (t 1)) (e.symm (t 2))) hrow
  rw [smallCoordinateSet_triple] at hproperty
  have h := SmallTripleExtensionProperty.full_ring e phi
    {e.symm (t 0),e.symm (t 1),e.symm (t 2)} hproperty
  simpa only [Finset.image_insert, Finset.image_singleton, RingEquiv.apply_symm_apply] using h

end D1Bound5
end
