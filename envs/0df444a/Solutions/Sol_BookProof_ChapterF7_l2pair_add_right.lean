-- Prove2me | solution 1 for BookProof.ChapterF7.l2pair_add_right
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:07:05.598248+00:00
-- url     : https://prove2.me/submissions/fb992534-4676-470d-b95a-15b30add5cdb

-- Generated from ChapterF7.lean — solution of BookProof.ChapterF7.l2pair_add_right
import Mathlib
import Definitions.Def_ChapterF7
import Theorems.Thm_BookProof_ChapterF7_l2pair_integrable
open BookProof.ChapterF7



open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (f g₁ g₂ : 𝓢(ℝ, ℂ)) :
    l2pair f (g₁ + g₂) = l2pair f g₁ + l2pair f g₂ := by

  unfold l2pair
  rw [← integral_add (l2pair_integrable f g₁) (l2pair_integrable f g₂)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [SchwartzMap.add_apply]
  ring
