-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.small_pair_excludes_three_bounded
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:18:07.356271+00:00
-- url     : https://prove2.me/submissions/f29a9c5f-8f9c-431b-b176-73fba84beb39

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
import Definitions.Def_D1Bound5_SmallPairClassificationCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairClassificationData_Definitions
import Definitions.Def_D1Bound5_SmallPairClassification_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphSymmetry_Definitions
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
import Theorems.Thm_D1Bound5_IsD1Tuple_small_pair_classification
import Theorems.Thm_D1Bound5_ProperCommonExtension_map_equiv
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv
import Theorems.Thm_D1Bound5_smallPairTable_graph_property_full_ring

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt







theorem smallCoordinateSet_pair {tau nu : ℤ} (a b : QuadInt tau nu) :
    smallCoordinateSet tau nu (pairCoordinates a b) = {a,b} := by
  simp [smallCoordinateSet, pairCoordinates]



end D1Bound5
end
section
open scoped NumberField Classical
open Module

namespace D1Bound5
open QuadInt

/-- An arbitrary nondegenerate pair of small algebraic integers in an
imaginary quadratic full ring cannot have three mutually compatible proper
extensions in the closed annulus with radii 3 and 10^550. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 2 → 𝓞 K) (ha : IsD1Tuple a)
    (hsmall : ∀ i, ‖phi (a i : K)‖ < 3)
    (hnondeg : a 0*a 1+1 ≠ 0)
    (t : Fin 3 → 𝓞 K) (ht : IsD1Tuple t)
    (hproper : ∀ i, ProperCommonExtension {a 0,a 1} (t i))
    (hlarge : ∀ i, 3 ≤ ‖phi (t i : K)‖)
    (hbound : ∀ i, ‖phi (t i : K)‖^2 ≤ (10 : ℝ)^1100) : False := by
  classical
  obtain ⟨tau, nu, e, hmodel, hrow⟩ :=
    IsD1Tuple.small_pair_classification hK phi a ha hsmall hnondeg
  have hproperty := smallPairTable_graph_property_full_ring hK phi e hmodel
    (pairCoordinates (e.symm (a 0)) (e.symm (a 1))) hrow
  rw [smallCoordinateSet_pair] at hproperty
  let s : Fin 3 → QuadInt tau nu := fun i => e.symm (t i)
  have hst : IsD1Tuple s := by
    refine ⟨e.symm.injective.comp ht.1, ?_, ?_⟩
    · intro i hz
      apply ht.2.1 i
      apply e.symm.injective
      simpa only [map_zero] using hz
    · intro i j hij
      obtain ⟨r, hr⟩ := ht.2.2 i j hij
      exact ⟨e.symm r, by simpa only [map_mul, map_add, map_one] using congrArg e.symm hr⟩
  have hnorm (i : Fin 3) : ‖phi (t i : K)‖^2 = ((s i).norm : ℝ) := by
    simpa only [s, RingEquiv.apply_symm_apply] using
      norm_sq_full_ring_equiv e phi (e.symm (t i))
  apply hproperty s hst
  · intro i
    have h := ProperCommonExtension.map_equiv e.symm {a 0,a 1} (t i) (hproper i)
    simpa only [Finset.image_insert, Finset.image_singleton] using h
  · intro i
    have h := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 3) (hlarge i)
    have hreal : (9 : ℝ) ≤ ((s i).norm : ℝ) := by nlinarith only [h, hnorm i]
    exact_mod_cast hreal
  · intro i
    have h := hbound i
    rw [hnorm i] at h
    exact_mod_cast h



end D1Bound5
end

