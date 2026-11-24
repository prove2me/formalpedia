-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qh_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:23.720979+00:00
-- url     : https://prove2.me/submissions/6924b47e-9648-4862-8b40-db70847a03e5

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhDetZpowMem
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QhMemDualWeyl
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_generic
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qh_det_ne
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
    (hQ : algebraMap _ (GLCoord R n) (rename Prod.swap Q) ∈ inducedSections R (fun a => (ν a : ℤ)))
    (l j : Fin n) (hlj : l < j) :
    Formalism.GradedWeylDivisibility.colAddGen R l j Q = rename some Q := by
  have h := qh_generic (B := MvPolynomial (Option (Fin n × Fin n)) R)
    (Matrix.transvection j l (X none)) (Matrix.of fun a c : Fin n => X (some (c, a)))
    (fun a c hac => by
      have : ¬ (j = a ∧ l = c) := by rintro ⟨rfl, rfl⟩; exact absurd hlj (not_lt.2 hac.le)
      simp [Matrix.transvection, hac.ne, this])
    (fun a => by
      have : ¬ (j = a ∧ l = a) := by rintro ⟨rfl, h⟩; exact hlj.ne h
      simp [Matrix.transvection, this])
    (qh_det_ne (rename some : MvPolynomial (Fin n × Fin n) R →ₐ[R] _).toRingHom
      (rename_injective _ (Option.some_injective _)) |> fun h => by simpa using h) Q ν hQ
  have e3 : (∏ a, (Matrix.transvection j l (X none : MvPolynomial (Option (Fin n × Fin n)) R)) a a ^ ν a) = 1 := by
    apply Finset.prod_eq_one
    intro a _
    have : ¬ (j = a ∧ l = a) := by rintro ⟨rfl, h⟩; exact hlj.ne h
    simp [Matrix.transvection, this]
  rw [e3, one_mul] at h
  have e1 : Formalism.GradedWeylDivisibility.colAddGen R l j Q = aeval (fun v : Fin n × Fin n => ((Matrix.transvection j l (X none)) *
      (Matrix.of fun a c : Fin n => (X (some (c, a)) : MvPolynomial (Option (Fin n × Fin n)) R)) :
        Matrix (Fin n) (Fin n) (MvPolynomial (Option (Fin n × Fin n)) R)) v.2 v.1) Q := by
    rw [Formalism.GradedWeylDivisibility.colAddGen]; congr 2; funext v
    by_cases hv : v.2 = j
    · rw [if_pos hv, hv, Matrix.transvection_mul_apply_same]
      simp [← hv]
    · rw [if_neg hv, Matrix.transvection_mul_apply_of_ne _ _ _ _ hv]
      simp
  rw [e1, h, ← aeval_X_left_apply (rename some Q), aeval_rename]
  rfl
end Formalism.InvariantFactorPaths.ColumnFamilies
