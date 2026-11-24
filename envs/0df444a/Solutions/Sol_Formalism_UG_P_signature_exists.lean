-- Prove2me | solution 1 for Formalism.UG.P.signature_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:09:26.294208+00:00
-- url     : https://prove2.me/submissions/d02c1f97-6b8b-4d7c-b31b-1de9f08d23f8

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Theorems.Thm_Formalism_UG_P_sigex_cT_conj_eq
import Theorems.Thm_Formalism_UG_P_herm_diag
import Theorems.Thm_Formalism_UG_P_eig_ne_zero
import Theorems.Thm_Formalism_UG_P_sign_pos
import Theorems.Thm_Formalism_UG_P_sign_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.UG Formalism.UG.P
open Matrix
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.SigExists := by
  unfold Formalism.UG.SigExists
  intro n _ _ J hJ hdet
  unfold Formalism.UG.IsHerm at hJ
  unfold Formalism.UG.HasSignature
  unfold Formalism.UG.Jpq
  have hH : J.IsHermitian := (sigex_cT_conj_eq J).symm.trans hJ
  have hU : ((hH.eigenvectorUnitary : Matrix n n ℂ))ᴴ * (hH.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
    have h := Unitary.star_mul_self_of_mem hH.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose] at h
  obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix n n ℂ,
      Q = (hH.eigenvectorUnitary : Matrix n n ℂ) * diagonal (scal hH.eigenvalues) := ⟨_, rfl⟩
  have hQ : Qᴴ * J * Q = diagonal (fun i => ((hH.eigenvalues i / |hH.eigenvalues i| : ℝ) : ℂ)) := by
    rw [hQdef]
    exact herm_diag hH
  obtain ⟨e, he⟩ : ∃ e : n ≃ Fin (Fintype.card {i // 0 < hH.eigenvalues i}) ⊕
      Fin (Fintype.card {i // ¬ 0 < hH.eigenvalues i}),
      e = (Equiv.sumCompl (fun i => 0 < hH.eigenvalues i)).symm.trans
        (Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _)) := ⟨_, rfl⟩
  have hinl : ∀ a, e.symm (Sum.inl a) =
      ((Fintype.equivFin {i // 0 < hH.eigenvalues i}).symm a : n) := by
    intro a
    rw [he]
    first | rfl | simp
  have hinr : ∀ a, e.symm (Sum.inr a) =
      ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a : n) := by
    intro a
    rw [he]
    first | rfl | simp
  have hdetQ : IsUnit (reindex e e Q).det := by
    rw [Matrix.det_reindex_self, hQdef, Matrix.det_mul, Matrix.det_diagonal]
    refine IsUnit.mul (Matrix.isUnit_det_of_left_inverse hU) ?_
    rw [isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _
    have h1 : hH.eigenvalues i ≠ 0 := eig_ne_zero hH hdet i
    simp only [scal, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (Real.sqrt_pos.mpr (abs_pos.mpr h1)).ne'
  refine ⟨_, _, e, Matrix.nonsingInvUnit _ hdetQ, ?_⟩
  change Formalism.UG.cT (starRingEnd ℂ) (reindex e e Q) * reindex e e J * reindex e e Q = _
  rw [sigex_cT_conj_eq]
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rw [hQ, Matrix.submatrix_diagonal_equiv]
  ext (a | a) (b | b)
  · simp only [Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply, Function.comp_apply, hinl,
      Sum.inl.injEq, Matrix.one_apply]
    split_ifs
    · rw [sign_pos ((Fintype.equivFin {i // 0 < hH.eigenvalues i}).symm a).2, Complex.ofReal_one]
    · rfl
  · simp [Matrix.diagonal_apply]
  · simp [Matrix.diagonal_apply]
  · simp only [Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, Function.comp_apply, hinr,
      Sum.inr.injEq, Matrix.neg_apply, Matrix.one_apply]
    split_ifs
    · have hx := ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a).2
      have hneg : hH.eigenvalues ((Fintype.equivFin {i // ¬ 0 < hH.eigenvalues i}).symm a : n) < 0 :=
        lt_of_le_of_ne (not_lt.mp hx) (eig_ne_zero hH hdet _)
      rw [sign_neg hneg]
      push_cast
      ring
    · simp
end Formalism.UG.P
