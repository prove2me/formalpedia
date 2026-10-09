-- Prove2me | solution 1 for BookProof.ChapterF7.i_comm_l2Symmetric
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:09:15.853088+00:00
-- url     : https://prove2.me/submissions/188450c6-50e0-4b71-8ae5-927b542d865f

-- Generated from ChapterF7.lean — solution of BookProof.ChapterF7.i_comm_l2Symmetric
import Mathlib
import Definitions.Def_ChapterF7
import Theorems.Thm_BookProof_ChapterF7_l2pair_sub_left
import Theorems.Thm_BookProof_ChapterF7_l2pair_sub_right
import Theorems.Thm_BookProof_ChapterF7_l2pair_smul_left
import Theorems.Thm_BookProof_ChapterF7_l2pair_smul_right
open BookProof.ChapterF7



open SchwartzMap MeasureTheory Complex
open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {K V : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ)}
    (hK : IsL2Symmetric K) (hV : IsL2Symmetric V) :
    IsL2Symmetric (Complex.I • (K.comp V - V.comp K)) := by

  intro f g
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply]
  rw [l2pair_smul_left, l2pair_smul_right, Complex.conj_I,
    l2pair_sub_left, l2pair_sub_right, hK, hV, hV, hK]
  ring
