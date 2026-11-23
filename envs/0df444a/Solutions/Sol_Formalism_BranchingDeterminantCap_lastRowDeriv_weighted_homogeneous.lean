-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.lastRowDeriv_weighted_homogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:38:15.14579+00:00
-- url     : https://prove2.me/submissions/f207abdb-2bea-4197-8370-ab9eb50effc1

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap
import Theorems.Thm_Formalism_BranchingDeterminantCap_bm_zcomp_bmZ
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
private theorem bm_whcWH_lemma_3 {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B) (m : B)
    (φ : MvPolynomial σ R) : IsWeightedHomogeneous w (weightedHomogeneousComponent w m φ) m := by
  classical
  intro d hd
  rw [coeff_weightedHomogeneousComponent] at hd
  split_ifs at hd with h
  · exact h
  · exact absurd rfl hd
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
theorem _root_.solution (R : Type*) [CommRing R] (n : ℕ) (l j : Fin n) (β : Fin n → ℤ) (F : BP R n)
    (hF : IsWeightedHomogeneous (zW n) F β) :
    IsWeightedHomogeneous (zW n) (bmZ R n l j F) (β + (Pi.single l 1 - Pi.single j 1)) := by
  have h := bm_zcomp_bmZ R n β l j F
  simp only [zcomp] at h
  rw [bm_whcSame_lemma hF] at h
  rw [← h]
  exact bm_whcWH_lemma_3 _ _ _
end Formalism.BranchingDeterminantCap
