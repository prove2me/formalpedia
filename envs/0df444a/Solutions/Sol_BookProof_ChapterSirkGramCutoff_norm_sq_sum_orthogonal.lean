-- Prove2me | solution 1 for BookProof.ChapterSirkGramCutoff.norm_sq_sum_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T06:28:15.977849+00:00
-- url     : https://prove2.me/submissions/3c92be8d-0d65-4c28-8fa3-1ce9566875c5

-- Generated from ChapterSirkGramCutoff.lean — solution of BookProof.ChapterSirkGramCutoff.norm_sq_sum_orthogonal
import Mathlib
import Definitions.Def_ChapterSirkGramCutoff
open BookProof.ChapterSirkGramCutoff










noncomputable section


open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

set_option maxHeartbeats 1000000 in
theorem solution {m : ℕ} (y : Fin m → E) (lam : Fin m → ℝ)
    (h : ∀ k l, ⟪y k, y l⟫_ℂ = if k = l then (lam l : ℂ) else 0)
    (s : Finset (Fin m)) (a : Fin m → ℂ) :
    ‖∑ k ∈ s, a k • y k‖ ^ 2 = ∑ k ∈ s, ‖a k‖ ^ 2 * lam k := by

  have hinner : ⟪∑ k ∈ s, a k • y k, ∑ k ∈ s, a k • y k⟫_ℂ
      = ((∑ k ∈ s, ‖a k‖ ^ 2 * lam k : ℝ) : ℂ) := by
    rw [sum_inner]
    push_cast
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [inner_sum, Finset.sum_eq_single k]
    · rw [inner_smul_left, inner_smul_right, h k k, if_pos rfl, ← mul_assoc,
        RCLike.conj_mul]
      norm_num
    · intro l _ hlk
      rw [inner_smul_left, inner_smul_right, h k l, if_neg (Ne.symm hlk)]
      ring
    · intro hk'
      exact absurd hk hk'
  have h2 := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (x := ∑ k ∈ s, a k • y k)
  rw [hinner] at h2
  have h3 : ((∑ k ∈ s, ‖a k‖ ^ 2 * lam k : ℝ) : ℂ)
      = ((‖∑ k ∈ s, a k • y k‖ ^ 2 : ℝ) : ℂ) := by push_cast at h2 ⊢; exact h2
  exact_mod_cast h3.symm
