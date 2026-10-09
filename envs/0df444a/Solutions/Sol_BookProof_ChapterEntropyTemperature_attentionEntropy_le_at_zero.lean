-- Prove2me | solution 1 for BookProof.ChapterEntropyTemperature.attentionEntropy_le_at_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:40:59.00159+00:00
-- url     : https://prove2.me/submissions/d8269f5b-621d-47e0-b356-2678c6fa8448
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterEntropyTemperature.lean — solution of BookProof.ChapterEntropyTemperature.attentionEntropy_le_at_zero
import Mathlib
import Definitions.Def_ChapterEntropyTemperature
import Theorems.Thm_BookProof_ChapterEntropyTemperature_attentionEntropy_antitoneOn
open BookProof.ChapterEntropyTemperature



open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (s : Fin m → ℝ) (i : Fin m) {beta : ℝ}
    (hbeta : 0 ≤ beta) : attentionEntropy beta s ≤ attentionEntropy 0 s := attentionEntropy_antitoneOn s i (Set.self_mem_Ici) (Set.mem_Ici.2 hbeta) hbeta
