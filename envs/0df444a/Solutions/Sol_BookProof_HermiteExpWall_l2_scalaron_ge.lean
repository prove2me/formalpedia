-- Prove2me | solution 1 for BookProof.HermiteExpWall.l2_scalaron_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:34.55469+00:00
-- url     : https://prove2.me/submissions/fa953715-94b2-4f15-b363-ad5d6bdd27b6

-- Generated from ChapterHermiteExpWall.lean — solution of BookProof.HermiteExpWall.l2_scalaron_ge
import Mathlib
import Definitions.Def_ChapterHermiteExpWall
import Theorems.Thm_BookProof_HermiteExpWall_l2_psi_sq
import Theorems.Thm_BookProof_HermiteExpWall_l2_psi_pos
import Theorems.Thm_BookProof_HermiteExpWall_memLp_psi
import Theorems.Thm_BookProof_HermiteExpWall_memLp_scalaron_psi
import Theorems.Thm_BookProof_HermiteExpWall_integral_mul_le_l2_mul_l2
import Theorems.Thm_BookProof_HermiteExpWall_quadForm_scalaron_ge
import Theorems.Thm_BookProof_Starobinsky_starobinskyV_nonneg
import Definitions.Def_ChapterHermiteFunctions
import Definitions.Def_ChapterQgHermiteCore
import Definitions.Def_ChapterGhostField
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterStarobinskyPotential
open BookProof.HermiteExpWall




open MeasureTheory Polynomial
open BookProof.HermiteCore BookProof.Starobinsky BookProof.QgHermiteCore
open BookProof.HermiteProductCore
open BookProof.GhostField
open BookProof.Starobinsky

noncomputable section

set_option maxHeartbeats 1000000 in

theorem solution (M alpha : ℝ) (hM : 0 < M) (halpha : 0 < alpha) (N : ℕ) :
    (M ^ 4 / (16 * alpha)) *
        ((8 * (Real.sqrt (2 / 3) / M) ^ 8 / 315) * (N : ℝ) ^ 4 - 1) * l2 (psi N)
      ≤ l2 (fun x => starobinskyV M alpha x * psi N x) := by
  have hVnn : ∀ x, 0 ≤ starobinskyV M alpha x := fun x => starobinskyV_nonneg halpha x
  have hcs := integral_mul_le_l2_mul_l2 (fun x => starobinskyV M alpha x * psi N x) (psi N)
    (memLp_scalaron_psi M alpha hM N) (memLp_psi N)
  have hform : ∫ x, ‖starobinskyV M alpha x * psi N x‖ * ‖psi N x‖
      = ∫ x : ℝ, starobinskyV M alpha x * psi N x ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hVnn x)]
    rcases abs_cases (psi N x) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> ring
  rw [hform] at hcs
  have hq := quadForm_scalaron_ge M alpha hM halpha N
  have hpos := l2_psi_pos N
  have hsq := l2_psi_sq N
  refine le_of_mul_le_mul_right ?_ hpos
  have hkey : (M ^ 4 / (16 * alpha)) *
      ((8 * (Real.sqrt (2 / 3) / M) ^ 8 / 315) * (N : ℝ) ^ 4 - 1) * l2 (psi N) * l2 (psi N)
      = (M ^ 4 / (16 * alpha)) *
        ((8 * (Real.sqrt (2 / 3) / M) ^ 8 / 315) * (N : ℝ) ^ 4 - 1) * gaussMoment (2 * N) := by
    rw [← hsq]; ring
  rw [hkey]
  linarith [hq, hcs]
