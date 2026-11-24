-- Prove2me | solution 1 for Formalism.REAL.diagChar_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:43:06.611572+00:00
-- url     : https://prove2.me/submissions/40b548f3-11ac-46c1-ab62-2cf6bd457c6a

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementB
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_HWDiag
import Theorems.Thm_Formalism_REAL_HWDiag_charpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.REAL
private theorem epow_zero_apply {A : Type*} [Ring A] {n : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin n) : epow E 0 a b = if a = b then 1 else 0 := by
  first | rfl | simp [epow]
private theorem sum_Amat_smul_eq_smul_sub_sum_gt {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (l : Fin n → ℂ) (y : Fin n → V) (a : Fin n) :
    ∑ c, Amat l a c • y c = l a • y a - ∑ c ∈ univ.filter (fun b => a < b), y c := by
  have hterm : ∀ c, Amat l a c • y c =
      (if c = a then l a • y c else 0) - (if a < c then y c else 0) := by
    intro c
    simp only [Amat, Matrix.of_apply]
    rcases lt_trichotomy c a with hca | hca | hca
    · simp [hca.ne, hca.ne', not_lt.mpr hca.le]
    · subst hca
      simp
    · simp [hca.ne, hca.ne', hca]
  rw [Finset.sum_congr rfl (fun c _ => hterm c), Finset.sum_sub_distrib, Finset.sum_filter]
  simp
end Formalism.REAL
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (h : HWDiag) : DiagChar := by
  unfold HWDiag at h
  unfold DiagChar
  intro V _i1 _i2 n E ν v hE hv a
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin n) ℂ, M = Amat (lsh ν) := ⟨_, rfl⟩
  have hrec : ∀ (k : ℕ) (b : Fin n),
      epow E (k + 1) b b v = ∑ c, M b c • epow E k c c v := by
    intro k b
    first
    | rw [h V n E ν v hE hv k b, hM, sum_Amat_smul_eq_smul_sub_sum_gt]
    | (rw [h V n E ν v hE hv k b, hM]; simp only [sum_Amat_smul_eq_smul_sub_sum_gt])
  have hpow : ∀ (k : ℕ) (b : Fin n), epow E k b b v = ∑ c, (M ^ k) b c • v := by
    intro k
    induction k with
    | zero =>
      intro b
      simp [epow_zero_apply, Matrix.one_apply]
    | succ k ih =>
      intro b
      rw [hrec, pow_succ']
      simp only [ih, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
      exact Finset.sum_comm
  have hchar : (∏ s : Fin n, (Polynomial.X - Polynomial.C (lsh ν s))) = M.charpoly := by
    rw [hM, HWDiag_charpoly]
  have hdeg : M.charpoly.natDegree < n + 1 := by
    have hd := Matrix.charpoly_natDegree_eq_dim M
    rw [Fintype.card_fin] at hd
    omega
  have hzero : Polynomial.aeval M M.charpoly = 0 := Matrix.aeval_self_charpoly M
  rw [Polynomial.aeval_eq_sum_range' hdeg] at hzero
  have hentry : ∀ c : Fin n, ∑ i ∈ range (n + 1), M.charpoly.coeff i * (M ^ i) a c = 0 := by
    intro c
    have hac := congrArg (fun N : Matrix (Fin n) (Fin n) ℂ => N a c) hzero
    simpa [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using hac
  rw [hchar]
  simp only [hpow, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, hentry, zero_smul, Finset.sum_const_zero]
end Formalism.REAL
