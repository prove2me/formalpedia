-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.commute_weightedComponent_of_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:03:04.456808+00:00
-- url     : https://prove2.me/submissions/9247ce37-7dae-464d-bc0e-dee6f133d471

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
theorem _root_.solution {R σ B : Type*} [CommRing R] [AddCommMonoid B] [IsRightCancelAdd B] (w : σ → B)
    (D : Module.End R (MvPolynomial σ R))
    (hD : ∀ m, IsWeightedHomogeneous w (D (monomial m 1)) (Finsupp.weight w m)) (β : B) :
    Commute (weightedHomogeneousComponent w β : Module.End R (MvPolynomial σ R)) D := by
  refine LinearMap.ext fun F => ?_
  show weightedHomogeneousComponent w β (D F) = D (weightedHomogeneousComponent w β F)
  induction F using MvPolynomial.induction_on' with
  | monomial u a =>
    have hm : monomial u a = a • monomial u (1 : R) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    have hDa : IsWeightedHomogeneous w (D (monomial u a)) (Finsupp.weight w u) := by
      rw [hm, map_smul]
      exact isWeightedHomogeneous_smul (hD u) a
    have hma : IsWeightedHomogeneous w (monomial u a) (Finsupp.weight w u) :=
      isWeightedHomogeneous_monomial w u a rfl
    by_cases h : Finsupp.weight w u = β
    · subst h
      rw [bm_whcSame_lemma hDa, bm_whcSame_lemma hma]
    · rw [bm_whcNe_lemma_2 hDa (Ne.symm h), bm_whcNe_lemma_2 hma (Ne.symm h), map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
end Formalism.BranchingDeterminantCap
