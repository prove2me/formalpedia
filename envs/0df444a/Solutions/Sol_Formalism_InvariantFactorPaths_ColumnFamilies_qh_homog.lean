-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_homog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:44:36.616967+00:00
-- url     : https://prove2.me/submissions/194cafbf-c497-42f1-965b-cd87554a76c6

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_generic
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_det_ne
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_phi_coeff
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_weight
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} {R : Type} [CommRing R]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution [IsDomain R] (Q : MvPolynomial (Fin n × Fin n) R) (ν : Fin n → ℕ)
    (hQ : algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ inducedSections R (fun a => (ν a : ℤ))) :
    IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW n n) Q ν := by
  have h := qh_generic (B := MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))
    (Matrix.diagonal fun a => X a) (Matrix.of fun a c : Fin n => C (X (c, a)))
    (fun a c hac => Matrix.diagonal_apply_ne _ hac.ne) (fun a => by simp)
    (qh_det_ne (C : _ →+* MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R)) (C_injective _ _)) Q ν hQ
  have e1 : aeval (fun v : Fin n × Fin n => ((Matrix.diagonal fun a => X a) *
      (Matrix.of fun a c : Fin n => (C (X (c, a)) : MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) :
        Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) v.2 v.1) Q
      = qhPhi R n Q := by
    rw [qhPhi]; congr 2; funext v; simp [Matrix.diagonal_mul]
  have e2 : aeval (fun v : Fin n × Fin n =>
      (Matrix.of fun a c : Fin n => (C (X (c, a)) : MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) v.2 v.1) Q
      = C Q := by
    have := MvPolynomial.comp_aeval_apply (R := R) (fun v : Fin n × Fin n => (X v : MvPolynomial (Fin n × Fin n) R))
      (IsScalarTower.toAlgHom R (MvPolynomial (Fin n × Fin n) R) (MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) Q
    rw [aeval_X_left_apply] at this
    exact this.symm
  have e3 : (∏ a, (Matrix.diagonal fun a => (X a : MvPolynomial (Fin n) (MvPolynomial (Fin n × Fin n) R))) a a ^ ν a) =
      monomial (Finsupp.equivFunOnFinite.symm ν) 1 := by
    rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
    simp
  rw [e1, e2, e3, mul_comm, C_mul_monomial, mul_one] at h
  intro d hd
  rw [qh_weight]
  by_contra hne
  apply hd
  rw [← qh_phi_coeff, h, coeff_monomial, if_neg, coeff_zero]
  intro heq
  apply hne
  rw [← heq]; rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
