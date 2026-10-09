-- Prove2me | solution 1 for BookProof.ChapterAttentionCoarseGrain.headOutput_merge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T16:38:43.529995+00:00
-- url     : https://prove2.me/submissions/04ab2bd3-e4a0-4ef2-a9a0-01ff0f22c500

-- Generated from ChapterAttentionCoarseGrain.lean — solution of BookProof.ChapterAttentionCoarseGrain.headOutput_merge
import Mathlib
import Definitions.Def_ChapterAttentionCoarseGrain
import Theorems.Thm_BookProof_ChapterAttentionCoarseGrain_observableExpectation_merge
import Definitions.Def_ChapterAttentionOutput
open BookProof.ChapterAttentionOutput
open BookProof.ChapterAttentionCoarseGrain



open scoped BigOperators

noncomputable section


open BookProof.ChapterObservableExpectation BookProof.ChapterSoftmaxSharpness

variable {m r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {m r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (f : Fin m → Fin r) (v : Fin r → E) :
    observableExpectation (mergeWeights f (scoreSoftmax beta s)) v
      = headOutput beta s (fun x => v (f x)) := observableExpectation_merge f (scoreSoftmax beta s) v
