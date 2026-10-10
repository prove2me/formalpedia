-- Prove2me | solution 1 for BookProof.Howland.howland_neg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:03:54.790288+00:00
-- url     : https://prove2.me/submissions/f9e98829-ce20-49a1-9131-bf4f44ae7f92

-- Generated from ChapterHowlandAutonomization.lean — solution of BookProof.Howland.howland_neg
import Mathlib
import Definitions.Def_ChapterHowlandAutonomization
import Theorems.Thm_BookProof_Howland_howland_add
open BookProof.Howland




open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [NormedAddCommGroup H]
variable {U : ℝ → ℝ → H → H}


@[simp] private theorem howland_zero (hU : IsPropagator U) (ψ : ℝ → H) :
    howland U 0 ψ = ψ := by
  funext t
  simp [howland, hU.refl]

set_option maxHeartbeats 1000000 in
theorem solution (hU : IsPropagator U) (σ : ℝ) (ψ : ℝ → H) :
    howland U (-σ) (howland U σ ψ) = ψ := by

  rw [howland_add hU, neg_add_cancel, howland_zero hU]
