-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.small_pair_classification
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T00:19:02.720671+00:00
-- url     : https://prove2.me/submissions/3d1fd6b1-da76-4c8f-a863-b958ed06c817

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_SmallPairClassificationCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairClassificationData_Definitions
import Definitions.Def_D1Bound5_SmallPairClassification_Definitions
import Theorems.Thm_D1Bound5_exists_imaginary_quadratic_ring_equiv
import Theorems.Thm_D1Bound5_full_small_pair_model_allowed
import Theorems.Thm_D1Bound5_nondegenerate_small_pair_parameter_bound
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv
import Theorems.Thm_D1Bound5_smallPair_classified_rectangular

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt





/-- Every nondegenerate compatible pair of small actual algebraic integers
belongs to one of the48explicit sign/conjugation orbits. The finite tables
are complete and maximality has removed all extra coordinate orders. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 2 → 𝓞 K) (ht : IsD1Tuple t)
    (hsmall : ∀ i, ‖phi (t i : K)‖ < 3)
    (hnondeg : t 0*t 1+1 ≠ 0) :
    ∃ (tau nu : ℤ) (e : QuadInt tau nu ≃+* 𝓞 K),
      (tau,nu) ∈ smallPairModels ∧
      pairCoordinates (e.symm (t 0)) (e.symm (t 1)) ∈ smallPairTable tau nu := by
  obtain ⟨tau, nu, htau, hpos, ⟨e⟩⟩ := exists_imaginary_quadratic_ring_equiv hK
  let s : Fin 2 → QuadInt tau nu := fun i => e.symm (t i)
  have hst : IsD1Tuple s := by
    refine ⟨e.symm.injective.comp ht.1, ?_, ?_⟩
    · intro i hz
      apply ht.2.1 i
      apply e.symm.injective
      simpa only [map_zero] using hz
    · intro i j hij
      obtain ⟨r, hr⟩ := ht.2.2 i j hij
      exact ⟨e.symm r, by simpa only [map_mul, map_add, map_one] using congrArg e.symm hr⟩
  have hnorm : ∀ i, (s i).norm ≤ 8 := by
    intro i
    have hN : ‖phi (t i : K)‖^2 = ((s i).norm : ℝ) := by
      simpa only [s, RingEquiv.apply_symm_apply] using
        norm_sq_full_ring_equiv e phi (e.symm (t i))
    have hproduct := mul_pos (sub_pos.mpr (hsmall i))
      (show (0 : ℝ) < 3+‖phi (t i : K)‖ by positivity)
    have hreal : ((s i).norm : ℝ) < 9 := by nlinarith only [hN, hproduct]
    have hint : (s i).norm < 9 := by exact_mod_cast hreal
    omega
  have hne : s 0 ≠ s 1 := fun h => (by decide : (0 : Fin 2) ≠ 1) (hst.1 h)
  have hnondegS : s 0*s 1+1 ≠ 0 := by
    intro h
    apply hnondeg
    apply e.symm.injective
    simpa only [map_mul, map_add, map_one, map_zero] using h
  have hroot := hst.2.2 0 1 (by decide)
  have hp := nondegenerate_small_pair_parameter_bound htau hpos (s 0) (s 1)
    (hst.2.1 0) (hst.2.1 1) hne (hnorm 0) (hnorm 1) hroot hnondegS
  refine ⟨tau, nu, e, full_small_pair_model_allowed e htau hpos hp.2.1 hp.2.2, ?_⟩
  exact smallPair_classified_rectangular htau hp.2.1 hp.2.2 (s 0) (s 1)
    (hst.2.1 0) (hst.2.1 1) hne hroot hnondegS (hnorm 0) (hnorm 1)

end D1Bound5
end
