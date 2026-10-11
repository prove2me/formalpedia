-- Prove2me | solution 1 for BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_of_le
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:45:11.020054+00:00
-- url     : https://prove2.me/submissions/bc0aad98-8c53-47c7-beae-9568ce48d0d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — solution of BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_max_ge_of_le
import Mathlib
import Definitions.Def_ChapterSoftmaxTemperatureMonotone
import Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_scoreSoftmax_monotone_of_max
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxTemperatureMonotone



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {beta gamma : ℝ} (hbg : beta ≤ gamma) (s : Fin m → ℝ)
    (j : Fin m) (hmax : ∀ l, s l ≤ s j) :
    scoreSoftmax beta s j ≤ scoreSoftmax gamma s j := scoreSoftmax_monotone_of_max s j hmax hbg
