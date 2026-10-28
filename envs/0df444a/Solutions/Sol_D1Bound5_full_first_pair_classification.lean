-- Prove2me | solution 1 for D1Bound5.full_first_pair_classification
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:28:20.026687+00:00
-- url     : https://prove2.me/submissions/61d49d67-3f06-416e-857a-84a85c74d445

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
import Definitions.Def_D1Bound5_FirstPairData_Definitions
import Definitions.Def_D1Bound5_OneSmallFiniteCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairClassification_Definitions
import Theorems.Thm_D1Bound5_exists_imaginary_quadratic_ring_equiv
import Theorems.Thm_D1Bound5_firstPair_classified_rectangular
import Theorems.Thm_D1Bound5_first_pair_of_large_discriminant
import Theorems.Thm_D1Bound5_full_small_pair_model_allowed
import Theorems.Thm_D1Bound5_norm_sq_full_ring_equiv

section
open scoped NumberField Classical
open Module

namespace D1Bound5
open QuadInt







/-- Every first pair in a full ring is rational (1,3) up to sign, or lies
in the complete finite first-pair table of one of the eleven maximal models.
The unused discriminant-31 table is empty, so it contributes no pairs. -/
theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ) (a b : 𝓞 K)
    (hsize :
      (‖phi (a : K)‖^2 = 1 ∧ 9 ≤ ‖phi (b : K)‖^2 ∧ ‖phi (b : K)‖^2 < 64) ∨
      (‖phi (a : K)‖^2 = 2 ∧ 9 ≤ ‖phi (b : K)‖^2 ∧ ‖phi (b : K)‖^2 < 16))
    (hroot : ∃ q : 𝓞 K, q*q = a*b+1) :
    (a = 1 ∧ b = 3) ∨ (a = -1 ∧ b = -3) ∨
      ∃ (tau nu : ℤ) (e : QuadInt tau nu ≃+* 𝓞 K),
        (tau,nu) ∈ smallPairModels ∧
        firstPairCoordinates (e.symm a) (e.symm b) ∈ firstPairTable tau nu := by
  classical
  obtain ⟨tau,nu,htau,hd,⟨e⟩⟩ := exists_imaginary_quadratic_ring_equiv hK
  have hnorm (z : 𝓞 K) : ‖phi (z : K)‖^2 = ((e.symm z).norm : ℝ) := by
    simpa only [RingEquiv.apply_symm_apply] using norm_sq_full_ring_equiv e phi (e.symm z)
  have hN : FirstPairNorms (e.symm a) (e.symm b) := by
    rw [hnorm a, hnorm b] at hsize
    rcases hsize with h | h
    · left
      have ha : (e.symm a).norm = 1 := by exact_mod_cast h.1
      have hb : 9 ≤ (e.symm b).norm := by exact_mod_cast h.2.1
      have hc : (e.symm b).norm < 64 := by exact_mod_cast h.2.2
      exact ⟨ha,hb,by omega⟩
    · right
      have ha : (e.symm a).norm = 2 := by exact_mod_cast h.1
      have hb : 9 ≤ (e.symm b).norm := by exact_mod_cast h.2.1
      have hc : (e.symm b).norm < 16 := by exact_mod_cast h.2.2
      exact ⟨ha,hb,by omega⟩
  have hroot' : ∃ q : QuadInt tau nu, q*q = e.symm a*e.symm b+1 := by
    obtain ⟨q,hq⟩ := hroot
    exact ⟨e.symm q, by simpa only [map_mul,map_add,map_one] using congrArg e.symm hq⟩
  have hrational (h : (e.symm a = 1 ∧ e.symm b = 3) ∨
      (e.symm a = -1 ∧ e.symm b = -3)) : (a = 1 ∧ b = 3) ∨ (a = -1 ∧ b = -3) := by
    rcases h with h | h
    · left
      constructor
      · simpa only [RingEquiv.apply_symm_apply, map_one] using congrArg e h.1
      · simpa only [RingEquiv.apply_symm_apply, map_ofNat] using congrArg e h.2
    · right
      constructor
      · simpa only [RingEquiv.apply_symm_apply, map_neg, map_one] using congrArg e h.1
      · simpa only [RingEquiv.apply_symm_apply, map_neg, map_ofNat] using congrArg e h.2
  by_cases hcut : discriminant tau nu ≤ 32
  · have hnu : 1 ≤ nu ∧ nu ≤ 8 := by
      rcases htau with rfl | rfl <;> simp only [discriminant] at hd hcut <;> omega
    have hc := firstPair_classified_rectangular htau hnu.1 hnu.2 _ _ hN hroot'
    rcases hc with h | h | h
    · exact (hrational (Or.inl h)).elim Or.inl (fun h => Or.inr (Or.inl h))
    · exact (hrational (Or.inr h)).elim Or.inl (fun h => Or.inr (Or.inl h))
    · exact Or.inr (Or.inr ⟨tau,nu,e,full_small_pair_model_allowed e htau hd hnu.1 hnu.2,h⟩)
  · have h := hrational (first_pair_of_large_discriminant (lt_of_not_ge hcut) _ _ hN hroot')
    exact h.elim Or.inl (fun h => Or.inr (Or.inl h))

end D1Bound5
end
