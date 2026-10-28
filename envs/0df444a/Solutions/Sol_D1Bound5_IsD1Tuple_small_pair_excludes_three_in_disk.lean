-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.small_pair_excludes_three_in_disk
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:16:03.405307+00:00
-- url     : https://prove2.me/submissions/b09454c8-1845-4bce-b10c-71e862496e42

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
import Theorems.Thm_D1Bound5_IsD1Tuple_small_pair_excludes_three_bounded
import Theorems.Thm_D1Bound5_QuadInt_norm_nonneg

section
open scoped NumberField Classical
open Module

namespace D1Bound5
open QuadInt



/-- The same complete finite exclusion with the radius stated directly. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (a : Fin 2 → 𝓞 K) (ha : IsD1Tuple a)
    (hsmall : ∀ i, ‖phi (a i : K)‖ < 3)
    (hnondeg : a 0*a 1+1 ≠ 0)
    (t : Fin 3 → 𝓞 K) (ht : IsD1Tuple t)
    (hproper : ∀ i, ProperCommonExtension {a 0,a 1} (t i))
    (hlarge : ∀ i, 3 ≤ ‖phi (t i : K)‖)
    (hbound : ∀ i, ‖phi (t i : K)‖ ≤ (10 : ℝ)^550) : False := by
  apply IsD1Tuple.small_pair_excludes_three_bounded hK phi a ha hsmall hnondeg
    t ht hproper hlarge
  intro i
  calc
    ‖phi (t i : K)‖^2 = ‖phi (t i : K)‖*‖phi (t i : K)‖ := pow_two _
    _ ≤ (10 : ℝ)^550*(10 : ℝ)^550 :=
      mul_self_le_mul_self (_root_.norm_nonneg _) (hbound i)
    _ = (10 : ℝ)^1100 := by rw [← pow_add]

end D1Bound5
end
