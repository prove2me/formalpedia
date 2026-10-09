-- Prove2me | solution 1 for BookProof.ChapterF7.l2pair_add_left
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:07:04.581794+00:00
-- url     : https://prove2.me/submissions/7e048ccf-e953-4cc3-a5da-51cd2bae448b

-- Generated from ChapterF7.lean — solution of BookProof.ChapterF7.l2pair_add_left
import Mathlib
import Definitions.Def_ChapterF7
import Theorems.Thm_BookProof_ChapterF7_l2pair_integrable
open BookProof.ChapterF7



open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (f₁ f₂ g : 𝓢(ℝ, ℂ)) :
    l2pair (f₁ + f₂) g = l2pair f₁ g + l2pair f₂ g := by

  unfold l2pair
  rw [← integral_add (l2pair_integrable f₁ g) (l2pair_integrable f₂ g)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [SchwartzMap.add_apply, map_add]
  ring
