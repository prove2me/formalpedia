-- Prove2me | solution 1 for BookProof.ChapterF7.anticomm_l2Symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:08:25.387785+00:00
-- url     : https://prove2.me/submissions/d18e71a9-bc19-467c-bff1-dbe2d5e1d2eb

-- Generated from ChapterF7.lean — solution of BookProof.ChapterF7.anticomm_l2Symmetric
import Mathlib
import Definitions.Def_ChapterF7
import Theorems.Thm_BookProof_ChapterF7_l2pair_add_left
import Theorems.Thm_BookProof_ChapterF7_l2pair_add_right
open BookProof.ChapterF7



open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {K V : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)}
    (hK : IsL2Symmetric K) (hV : IsL2Symmetric V) :
    IsL2Symmetric (K.comp V + V.comp K) := by

  intro f g
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply]
  rw [l2pair_add_left, l2pair_add_right, hK, hV, hV, hK]
  ring
