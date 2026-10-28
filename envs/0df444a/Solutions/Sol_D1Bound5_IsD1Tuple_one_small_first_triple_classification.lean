-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.one_small_first_triple_classification
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:21:09.107861+00:00
-- url     : https://prove2.me/submissions/71d0953d-2c4c-47b2-8a8c-463304a4a175

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
import Definitions.Def_D1Bound5_FirstPairData_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_OneSmallRows_Definitions
import Definitions.Def_D1Bound5_OneSmallSymmetry_Definitions
import Definitions.Def_D1Bound5_SmallPairClassification_Definitions
import Theorems.Thm_D1Bound5_firstPairTable_third_rows
import Theorems.Thm_D1Bound5_full_first_pair_classification
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv

section
open scoped NumberField Classical
open Module

namespace D1Bound5
open QuadInt

/-- Complete actual-full-ring classification after the analytic first-pair
and third-entry size reductions. Only the rational pair remains separate. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 3 → 𝓞 K) (ht : IsD1Tuple t)
    (hsize :
      (‖phi (t 0 : K)‖^2 = 1 ∧ 9 ≤ ‖phi (t 1 : K)‖^2 ∧ ‖phi (t 1 : K)‖^2 < 64) ∨
      (‖phi (t 0 : K)‖^2 = 2 ∧ 9 ≤ ‖phi (t 1 : K)‖^2 ∧ ‖phi (t 1 : K)‖^2 < 16))
    (hbound : ‖phi (t 2 : K)‖^2 < 225)
    (horder : ‖phi (t 1 : K)‖^2 ≤ ‖phi (t 2 : K)‖^2) :
    (t 0 = 1 ∧ t 1 = 3) ∨ (t 0 = -1 ∧ t 1 = -3) ∨
      ∃ (tau nu : ℤ) (e : QuadInt tau nu ≃+* 𝓞 K),
        (tau,nu) ∈ smallPairModels ∧
        OneSmallNormalizedThirdRows (e.symm (t 0)) (e.symm (t 1)) (e.symm (t 2)) := by
  classical
  obtain h | h | ⟨tau,nu,e,hmodel,hrow⟩ := full_first_pair_classification hK phi
    (t 0) (t 1) hsize (ht.2.2 0 1 (by decide))
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  right; right
  refine ⟨tau,nu,e,hmodel,?_⟩
  have hnorm (i : Fin 3) : ‖phi (t i : K)‖^2 = ((e.symm (t i)).norm : ℝ) := by
    simpa only [RingEquiv.apply_symm_apply] using norm_sq_full_ring_equiv e phi (e.symm (t i))
  apply firstPairTable_third_rows hmodel _ _ _ hrow
  · rw [hnorm 2] at hbound
    have hi : (e.symm (t 2)).norm < 225 := by exact_mod_cast hbound
    omega
  · rw [hnorm 1,hnorm 2] at horder
    exact_mod_cast horder
  · intro h
    exact (by decide : (2 : Fin 3) ≠ 0) (ht.1 (e.symm.injective h))
  · intro h
    exact (by decide : (2 : Fin 3) ≠ 1) (ht.1 (e.symm.injective h))
  · constructor
    · obtain ⟨q,hq⟩ := ht.2.2 0 2 (by decide)
      exact ⟨e.symm q,by simpa only [map_mul,map_add,map_one] using congrArg e.symm hq⟩
    · obtain ⟨q,hq⟩ := ht.2.2 1 2 (by decide)
      exact ⟨e.symm q,by simpa only [map_mul,map_add,map_one] using congrArg e.symm hq⟩





end D1Bound5
end
