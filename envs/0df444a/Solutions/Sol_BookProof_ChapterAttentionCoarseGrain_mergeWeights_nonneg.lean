-- Prove2me | solution 1 for BookProof.ChapterAttentionCoarseGrain.mergeWeights_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T04:40:53.411071+00:00
-- url     : https://prove2.me/submissions/5a04771a-ef07-4c09-99f5-fdc6cfb4f905

import Definitions.Def_ChapterObservableExpectation
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib
import Definitions.Def_ChapterAttentionCoarseGrain

open BookProof.ChapterAttentionCoarseGrain

theorem solution {m r : ℕ} {f : Fin m → Fin r} {p : Fin m → ℝ} (hp : ∀ x, 0 ≤ p x)
    (y : Fin r) : 0 ≤ mergeWeights f p y := by
  unfold mergeWeights
  exact Finset.sum_nonneg fun _ _ => hp _
