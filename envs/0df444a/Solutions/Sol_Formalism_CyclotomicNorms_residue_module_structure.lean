-- Prove2me | solution 1 for Formalism.CyclotomicNorms.residue_module_structure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:24:33.095302+00:00
-- url     : https://prove2.me/submissions/4bb2857e-94db-4bad-81ae-7a762b15c2a7

import Definitions.Def_Formalism_CyclotomicNorms_StatementTW
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_ResModule
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_zero_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_zero
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_blockExtend_succ_succ
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_exists_diag
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_trunc_normal
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_trunc_total
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_tt_pow_notMem
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_finrank_split
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_eq_bot_of_noTorsion
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_finrank_span_le
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_cyclic_of_socle
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_ker_lower
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_ker_kill
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_det_eq
import Theorems.Thm_Formalism_CyclotomicNorms_residueMatrixData_adj_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_zero_zero
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_zero_succ
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_succ_zero
attribute [local simp] Formalism.CyclotomicNorms.residueMatrixData.blockExtend_succ_succ

set_option autoImplicit false
open Polynomial Matrix
open Formalism Formalism.CyclotomicNorms
noncomputable section
open residueMatrixData
namespace Formalism.CyclotomicNorms
theorem _root_.solution : RESModule := by
  intro K' _ n a C Φ N hC hN hdim
  classical
  obtain ⟨P, Q, hP, hQ, d, hd⟩ := exists_diag (trunc_total (K' := K') (n := n)) a Φ
  choose k hk u hu hdu using fun i => trunc_normal (K' := K') (n := n) (d i)
  set T : TruncK K' n := Ideal.Quotient.mk (Ideal.span {(X : K'[X]) ^ n}) X with hT
  let w : Fin a → TruncK K' n := fun i => (((hu i).unit⁻¹ : (TruncK K' n)ˣ) : TruncK K' n)
  have hP2 : IsUnit (diagonal w * P).det := by
    rw [det_mul, det_diagonal]
    have : ∏ i, w i = ((∏ i, (hu i).unit⁻¹ : (TruncK K' n)ˣ) : TruncK K' n) := by
      rw [Units.coe_prod]
    rw [this]
    exact (Units.isUnit _).mul hP
  have hD2 : diagonal w * P * Φ * Q = diagonal (fun i => T ^ k i) := by
    rw [show diagonal w * P * Φ * Q = diagonal w * (P * Φ * Q) by simp only [Matrix.mul_assoc], hd,
      diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [w]
    rw [hdu i, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  have hkerL := ker_lower Φ _ Q k hk hP2 hQ hD2
  have hsplit := finrank_split (LinearMap.ker (Matrix.toLin' Φ)) N hN
  refine ⟨fun hTor => ?_, fun ha hsoc => ?_⟩
  · have hNb := eq_bot_of_noTorsion N hTor
    refine ⟨hNb, fun hdet => ?_⟩
    have h0 : Module.finrank K' ↥N = 0 := by rw [hNb]; exact Module.finrank_zero_of_subsingleton
    have hsum : ∑ i, k i ≤ C := by omega
    have hmem : T ^ (∑ i, k i) ∈ Ideal.span {T ^ (C + 1)} := by
      rw [← det_eq Φ _ Q k hD2]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hdet)
    exact tt_pow_notMem hsum hC hmem
  · obtain ⟨x, hx⟩ := cyclic_of_socle N hsoc
    refine ⟨⟨x, hx⟩, ?_⟩
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ k Finset.univ_nonempty
    by_contra hcon
    have hall : ∀ i j, adjugate Φ i j ∈ Ideal.span {T ^ (C + 1)} := by
      intro i j
      rw [adjugate_fin_succ_eq_det_submatrix]
      apply Ideal.mul_mem_left
      by_contra hm
      exact hcon ⟨j, i, a', rfl, by simpa using hm⟩
    have hmem := adj_mem Φ _ Q k hD2 _ hall i0
    have hxN : x ∈ N := by rw [hx]; exact Submodule.mem_span_singleton_self x
    have hNle : Module.finrank K' ↥N ≤ k i0 := by
      rw [hx]
      exact finrank_span_le x (ker_kill Φ _ Q k hP2 hQ hD2 (k i0) (fun i => hi0 i (Finset.mem_univ i)) x
        (hN hxN))
    have hsum := Finset.add_sum_erase Finset.univ k (Finset.mem_univ i0)
    have hle : ∑ j ∈ Finset.univ.erase i0, k j ≤ C := by omega
    exact tt_pow_notMem hle hC hmem
end Formalism.CyclotomicNorms
