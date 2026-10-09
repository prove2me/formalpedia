-- Prove2me | solution 1 for BookProof.ChapterEntropyTemperature.hasDerivAt_attentionEntropy_neg_heatCapacity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:40:57.893487+00:00
-- url     : https://prove2.me/submissions/bd965a89-6056-40cf-9e8f-cabbfe59e166
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterEntropyTemperature.lean — solution of BookProof.ChapterEntropyTemperature.hasDerivAt_attentionEntropy_neg_heatCapacity
import Mathlib
import Definitions.Def_ChapterEntropyTemperature
import Theorems.Thm_BookProof_ChapterEntropyTemperature_hasDerivAt_attentionEntropy
open BookProof.ChapterEntropyTemperature



open scoped BigOperators

noncomputable section


open BookProof.ChapterAttentionEntropy BookProof.ChapterSoftmaxSharpness

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {beta : ℝ} (hbeta : beta ≠ 0)
    (s : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (fun b : ℝ => attentionEntropy b s) (-(heatCapacity beta s / beta)) beta := by

  refine (hasDerivAt_attentionEntropy beta s i).congr_deriv ?_
  rw [heatCapacity]
  field_simp
