-- Prove2me | solution 1 for BookProof.ChapterAttentionMixture.multiHead_output_eq_mean
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T17:29:06.629563+00:00
-- url     : https://prove2.me/submissions/d1483b29-ebff-4c3f-a024-ae153612a0ca

-- Generated from ChapterAttentionMixture.lean — solution of BookProof.ChapterAttentionMixture.multiHead_output_eq_mean
import Mathlib
import Definitions.Def_ChapterAttentionMixture
import Theorems.Thm_BookProof_ChapterAttentionMixture_observableExpectation_mixture
import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterAttentionOutput
open BookProof.ChapterObservableExpectation
open BookProof.ChapterAttentionMixture



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (w : Fin H → ℝ) (beta : Fin H → ℝ)
    (s : Fin H → Fin m → ℝ) (v : Fin m → E) :
    observableExpectation (multiHead w beta s) v
      = ∑ h, w h • headOutput (beta h) (s h) v := observableExpectation_mixture w (fun h => scoreSoftmax (beta h) (s h)) v
