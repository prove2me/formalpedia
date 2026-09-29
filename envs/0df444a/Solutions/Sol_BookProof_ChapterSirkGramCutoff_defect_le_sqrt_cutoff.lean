-- Prove2me | solution 1 for BookProof.ChapterSirkGramCutoff.defect_le_sqrt_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:29:40.104666+00:00
-- url     : https://prove2.me/submissions/377c208d-6738-4906-91e4-05f1b4b0974b

-- Generated from ChapterSirkGramCutoff.lean — solution of BookProof.ChapterSirkGramCutoff.defect_le_sqrt_cutoff
import Mathlib
import Definitions.Def_ChapterSirkGramCutoff
import Theorems.Thm_BookProof_ChapterSirkGramCutoff_norm_sub_proj_le_of_mem_range
import Theorems.Thm_BookProof_ChapterSirkGramCutoff_dist_synthesis_retained_le
import Theorems.Thm_BookProof_ChapterSirkGramCutoff_synthesis_single
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
    (R : Finset (Fin m)) (hcut : ∀ k ∉ R, lam k ≤ tol)
    {d : ℕ} (V : EuclideanSpace ℂ (Fin d) →L[ℂ] E)
    (hV : (adjoint V).comp V = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin d)))
    (hmem : ∀ k ∈ R, ∃ z, V z = synthesis w (u k)) (i : Fin m) :
    ‖w i - V (adjoint V (w i))‖ ≤ Real.sqrt tol := by

  set c : EuclideanSpace ℂ (Fin m) := EuclideanSpace.single i (1 : ℂ) with hc
  have hnormc : ‖c‖ = 1 := by simp [hc]
  have hwi : synthesis w c = w i := synthesis_single i
  set y : E := ∑ k ∈ R, ⟪u k, c⟫_ℂ • synthesis w (u k) with hy
  have hyrange : ∃ z, V z = y := by
    have hmemS : ∀ k ∈ R, ⟪u k, c⟫_ℂ • synthesis w (u k) ∈
        LinearMap.range (V : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] E) := by
      intro k hk
      obtain ⟨z, hz⟩ := hmem k hk
      exact Submodule.smul_mem _ _ ⟨z, hz⟩
    have : y ∈ LinearMap.range (V : EuclideanSpace ℂ (Fin d) →ₗ[ℂ] E) :=
      Submodule.sum_mem _ hmemS
    obtain ⟨z, hz⟩ := this
    exact ⟨z, hz⟩
  have hclose : ‖w i - y‖ ≤ Real.sqrt tol := by
    have h := dist_synthesis_retained_le heig R hcut c
    rw [hwi, hnormc, mul_one] at h
    exact h
  exact le_trans (norm_sub_proj_le_of_mem_range V hV (w i) hyrange) hclose
