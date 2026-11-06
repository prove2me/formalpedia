-- Prove2me | solution 1 for BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-05T19:48:19.377057+00:00
-- url     : https://prove2.me/submissions/67eb65d5-70e3-4bf8-85d4-38742a34fea8

-- Generated from ChapterNsCutoffUniformity.lean — solution of BookProof.NsCutoffUniformity.norm_coeff_redFormPoly_le
import Mathlib
import Definitions.Def_ChapterNsCutoffUniformity
import Theorems.Thm_BookProof_NsCutoffUniformity_norm_coeff_redAdvectPoly_le
import Theorems.Thm_BookProof_NsCutoffUniformity_norm_coeff_redMomentumPoly_le
import Definitions.Def_ChapterNavierStokesFullEulerianFock
open BookProof.NsCutoffUniformity




open MvPolynomial BookProof.NsFullEuler

noncomputable section

variable {n : ℕ}

variable {n : ℕ}
variable {ι : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (nu : ℝ) {Λ : ℝ} {k : Fin 3 → ℝ} (hΛ : 0 ≤ Λ)
    (hk : ∀ j, |k j| ≤ Λ) (p : Fin n) (r : Fin 7) (m : Fin (n * 6) →₀ ℕ) :
    ‖coeff m (redFormPoly nu k n p r)‖ ≤ cutoffBound nu Λ := by

  have hvisc : (0 : ℝ) ≤ 3 * |nu| * Λ ^ 2 := by positivity
  have hlam : (0 : ℝ) ≤ 3 * Λ := by positivity
  rw [redFormPoly]
  split
  · refine (norm_coeff_redVisc_le nu hΛ hk p _ m).trans ?_
    unfold cutoffBound
    linarith
  · split
    · refine (norm_coeff_redAdvectPoly_le hk p _ m).trans ?_
      unfold cutoffBound
      linarith
    · refine (norm_coeff_redMomentumPoly_le hk p m).trans ?_
      unfold cutoffBound
      linarith
