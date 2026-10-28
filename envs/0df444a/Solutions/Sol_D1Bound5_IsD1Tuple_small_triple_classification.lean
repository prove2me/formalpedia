-- Prove2me | solution 1 for D1Bound5.IsD1Tuple.small_triple_classification
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:28:03.535155+00:00
-- url     : https://prove2.me/submissions/04a41d75-4b09-4997-affe-e6eb96ea986e

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
import Definitions.Def_D1Bound5_SmallTripleCheck_Definitions
import Definitions.Def_D1Bound5_SmallTripleData_Definitions
import Theorems.Thm_D1Bound5_exists_imaginary_quadratic_ring_equiv
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv
import Theorems.Thm_D1Bound5_smallTriple_classified_normalized
import Theorems.Thm_D1Bound5_squarefree_trace_zero_parameter

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000






















/-- Only five normalized coordinate models admit a small triple. The fifth
is the nonmaximal Gaussian order, excluded at the full-ring endpoint. -/
theorem smallTripleTable_models {tau nu : ℤ} {row : Finset (ℤ × ℤ)}
    (h : row ∈ smallTripleTable tau nu) :
    (tau = 0 ∧ nu = 1) ∨ (tau = 0 ∧ nu = 2) ∨ (tau = 0 ∧ nu = 4) ∨
    (tau = 1 ∧ nu = 1) ∨ (tau = 1 ∧ nu = 2) := by
  unfold smallTripleTable at h
  split_ifs at h <;> simp_all





































































end D1Bound5
end

section
open scoped NumberField
open Module

namespace D1Bound5
open QuadInt





/-- Full-ring small-triple classification: precisely four coordinate models
are possible, and the unordered triple lies in the explicit 24-entry table.
The models are the full rings for d = 1, 2, 3, 7 respectively. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ)
    (t : Fin 3 → 𝓞 K) (ht : IsD1Tuple t)
    (hsmall : ∀ i, ‖phi (t i : K)‖ < 3) :
    ∃ (tau nu : ℤ) (e : QuadInt tau nu ≃+* 𝓞 K),
      ((tau = 0 ∧ nu = 1) ∨ (tau = 0 ∧ nu = 2) ∨
       (tau = 1 ∧ nu = 1) ∨ (tau = 1 ∧ nu = 2)) ∧
      tripleCoordinates (e.symm (t 0)) (e.symm (t 1)) (e.symm (t 2)) ∈
        smallTripleTable tau nu := by
  obtain ⟨tau, nu, htau, hpos, ⟨e⟩⟩ := exists_imaginary_quadratic_ring_equiv hK
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
  have hrow := smallTriple_classified_normalized htau hpos s hst hnorm
  refine ⟨tau, nu, e, ?_, hrow⟩
  rcases smallTripleTable_models hrow with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases h with ⟨rfl, rfl⟩
    have hsf := squarefree_trace_zero_parameter e hpos
    have hu : IsUnit (2 : ℤ) := hsf 2 (by norm_num)
    norm_num [Int.isUnit_iff] at hu
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

end D1Bound5
end
