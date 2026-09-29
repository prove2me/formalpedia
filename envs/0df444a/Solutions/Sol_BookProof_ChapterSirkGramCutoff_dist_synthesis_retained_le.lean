-- Prove2me | solution 1 for BookProof.ChapterSirkGramCutoff.dist_synthesis_retained_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:25.862431+00:00
-- url     : https://prove2.me/submissions/20773036-602e-4740-bcd8-44dd56aab060

-- Generated from ChapterSirkGramCutoff.lean — solution of BookProof.ChapterSirkGramCutoff.dist_synthesis_retained_le
import Mathlib
import Definitions.Def_ChapterSirkGramCutoff
import Theorems.Thm_BookProof_ChapterSirkGramCutoff_norm_sq_sum_orthogonal
import Theorems.Thm_BookProof_ChapterSirkGramCutoff_inner_synthesis_gramEigen
import Theorems.Thm_BookProof_ChapterSirkGramCutoff_gramEigen_nonneg
import Theorems.Thm_BookProof_ChapterSirkGramCutoff_synthesis_eq_sum_gramEigen
open BookProof.ChapterSirkGramCutoff










noncomputable section


open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]






variable {m : ℕ} {w : Fin m → E}
variable {u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))} {lam : Fin m → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (heig : IsGramEigen w u lam) {tol : ℝ}
    (R : Finset (Fin m)) (hcut : ∀ k ∉ R, lam k ≤ tol) (c : EuclideanSpace ℂ (Fin m)) :
    ‖synthesis w c - ∑ k ∈ R, ⟪u k, c⟫_ℂ • synthesis w (u k)‖ ≤ Real.sqrt tol * ‖c‖ := by

  set a : Fin m → ℂ := fun k => ⟪u k, c⟫_ℂ with ha
  have hsplit : synthesis w c - ∑ k ∈ R, a k • synthesis w (u k)
      = ∑ k ∈ Rᶜ, a k • synthesis w (u k) := by
    rw [synthesis_eq_sum_gramEigen (u := u) c, ← Finset.sum_add_sum_compl R
      (fun k => a k • synthesis w (u k))]
    abel
  have hpar : ∑ k, ‖a k‖ ^ 2 = ‖c‖ ^ 2 := u.sum_sq_norm_inner_right c
  have hnn : ∀ k, 0 ≤ lam k := gramEigen_nonneg heig
  rcases Finset.eq_empty_or_nonempty Rᶜ with hRc | hRc
  · rw [hsplit, hRc]
    simp only [Finset.sum_empty, norm_zero]
    have h0 : 0 ≤ Real.sqrt tol := Real.sqrt_nonneg _
    positivity
  · obtain ⟨k0, hk0⟩ := hRc
    have htol : 0 ≤ tol :=
      le_trans (hnn k0) (hcut k0 (Finset.mem_compl.mp hk0))
    have hsq : ‖∑ k ∈ Rᶜ, a k • synthesis w (u k)‖ ^ 2 ≤ tol * ‖c‖ ^ 2 := by
      rw [norm_sq_sum_orthogonal (fun k => synthesis w (u k)) lam
        (inner_synthesis_gramEigen heig) Rᶜ a]
      calc ∑ k ∈ Rᶜ, ‖a k‖ ^ 2 * lam k
          ≤ ∑ k ∈ Rᶜ, ‖a k‖ ^ 2 * tol := by
            refine Finset.sum_le_sum fun k hk => ?_
            exact mul_le_mul_of_nonneg_left (hcut k (Finset.mem_compl.mp hk))
              (by positivity)
        _ = (∑ k ∈ Rᶜ, ‖a k‖ ^ 2) * tol := by rw [Finset.sum_mul]
        _ ≤ (∑ k, ‖a k‖ ^ 2) * tol := by
            refine mul_le_mul_of_nonneg_right ?_ htol
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun k _ _ => by positivity)
        _ = tol * ‖c‖ ^ 2 := by rw [hpar]; ring
    rw [hsplit]
    have hgoal : ‖∑ k ∈ Rᶜ, a k • synthesis w (u k)‖ ^ 2 ≤ (Real.sqrt tol * ‖c‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt htol]
      exact hsq
    have h1 := Real.sqrt_le_sqrt hgoal
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by positivity)] at h1
