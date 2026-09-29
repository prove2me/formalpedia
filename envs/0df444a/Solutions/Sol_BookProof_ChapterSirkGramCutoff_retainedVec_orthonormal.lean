-- Prove2me | solution 1 for BookProof.ChapterSirkGramCutoff.retainedVec_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T07:28:19.368509+00:00
-- url     : https://prove2.me/submissions/9933fba2-934f-4b7a-a45d-6982221c94ae

-- Generated from ChapterSirkGramCutoff.lean — solution of BookProof.ChapterSirkGramCutoff.retainedVec_orthonormal
import Mathlib
import Definitions.Def_ChapterSirkGramCutoff
import Theorems.Thm_BookProof_ChapterSirkGramCutoff_inner_synthesis_gramEigen
open BookProof.ChapterSirkGramCutoff










noncomputable section


open scoped InnerProductSpace
open BookProof.ChapterSirkGramWhitening
open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]






variable {m : ℕ} {w : Fin m → E}
variable {u : OrthonormalBasis (Fin m) ℂ (EuclideanSpace ℂ (Fin m))} {lam : Fin m → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (heig : IsGramEigen w u lam) {d : ℕ} {e : Fin d → Fin m}
    (he : Function.Injective e) (hpos : ∀ j, 0 < lam (e j)) :
    Orthonormal ℂ (retainedVec w u lam e) := by

  rw [orthonormal_iff_ite]
  intro j l
  have hjl : ⟪synthesis w (u (e j)), synthesis w (u (e l))⟫_ℂ
      = if j = l then (lam (e l) : ℂ) else 0 := by
    rw [inner_synthesis_gramEigen heig]
    by_cases h : j = l
    · simp [h]
    · simp only [h, if_false]
      exact if_neg fun hh => h (he hh)
  have hexp : ⟪retainedVec w u lam e j, retainedVec w u lam e l⟫_ℂ
      = (starRingEnd ℂ) ((Real.sqrt (lam (e j)) : ℂ)⁻¹) *
          (((Real.sqrt (lam (e l)) : ℂ))⁻¹ *
            ⟪synthesis w (u (e j)), synthesis w (u (e l))⟫_ℂ) := by
    simp only [retainedVec, inner_smul_left, inner_smul_right]
    ring
  rw [hexp, hjl]
  by_cases h : j = l
  · subst h
    have hp := hpos j
    have hsne : ((Real.sqrt (lam (e j)) : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      positivity
    have hsq : ((Real.sqrt (lam (e j)) : ℝ) : ℂ) * ((Real.sqrt (lam (e j)) : ℝ) : ℂ)
        = (lam (e j) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp.le]
    have hconj : (starRingEnd ℂ) (((Real.sqrt (lam (e j)) : ℝ) : ℂ)⁻¹)
        = (((Real.sqrt (lam (e j)) : ℝ) : ℂ))⁻¹ := by
      rw [map_inv₀, Complex.conj_ofReal]
    rw [if_pos rfl, if_pos rfl, hconj, ← hsq]
    field_simp
  · simp [h]
