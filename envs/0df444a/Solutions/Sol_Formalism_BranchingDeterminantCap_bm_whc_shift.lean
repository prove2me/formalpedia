-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_whc_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:04.58836+00:00
-- url     : https://prove2.me/submissions/52401a07-e3df-4dbc-a7b2-fce0eb40fb57

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_isWeightedHomogeneous_smul
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


section
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
namespace Formalism.BranchingDeterminantCap
private theorem bm_whcSame_lemma {R σ B : Type*} [CommRing R] [AddCommMonoid B] {w : σ → B} {m : B}
    {φ : MvPolynomial σ R} (h : IsWeightedHomogeneous w φ m) : weightedHomogeneousComponent w m φ = φ := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent]
  split_ifs with hd
  · rfl
  · by_contra hc
    exact hd (h (Ne.symm hc))
private theorem bm_whcNe_lemma_2 {R σ B : Type*} [CommRing R] [AddCommMonoid B] {w : σ → B} {m : B}
    {φ : MvPolynomial σ R} (h : IsWeightedHomogeneous w φ m) {k : B} (hk : k ≠ m) :
    weightedHomogeneousComponent w k φ = 0 := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_zero]
  split_ifs with hd
  · by_contra hc
    exact hk (hd.symm.trans (h hc))
  · rfl
section bmAList
variable {A : Type*} [Ring A]
end bmAList
section bmACap
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
end bmACap
section bmACap2
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
end bmACap2
section bmACap3
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
end bmACap3
end Formalism.BranchingDeterminantCap
end
end

set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R σ B : Type*} [CommRing R] [AddCommMonoid B] [IsRightCancelAdd B] (w : σ → B) (δ : B)
    (D : MvPolynomial σ R →ₗ[R] MvPolynomial σ R)
    (hD : ∀ m, IsWeightedHomogeneous w (D (monomial m 1)) (Finsupp.weight w m + δ)) (β : B)
    (F : MvPolynomial σ R) :
    weightedHomogeneousComponent w (β + δ) (D F) = D (weightedHomogeneousComponent w β F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    have hm : monomial u a = a • monomial u (1 : R) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    have hDa : IsWeightedHomogeneous w (D (monomial u a)) (Finsupp.weight w u + δ) := by
      rw [hm, map_smul]
      exact isWeightedHomogeneous_smul (hD u) a
    have hma : IsWeightedHomogeneous w (monomial u a) (Finsupp.weight w u) :=
      isWeightedHomogeneous_monomial w u a rfl
    by_cases h : Finsupp.weight w u = β
    · subst h
      rw [bm_whcSame_lemma hDa, bm_whcSame_lemma hma]
    · rw [bm_whcNe_lemma_2 hDa (fun h' => h (add_right_cancel h').symm), bm_whcNe_lemma_2 hma (Ne.symm h),
        map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
end Formalism.BranchingDeterminantCap
