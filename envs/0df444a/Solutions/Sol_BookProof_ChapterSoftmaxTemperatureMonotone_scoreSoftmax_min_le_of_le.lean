-- Prove2me | solution 1 for BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:45:11.977649+00:00
-- url     : https://prove2.me/submissions/c3cab3f6-9d1b-4d79-a1e9-cbd778c8659c

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — solution of BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_min_le_of_le
import Mathlib
import Definitions.Def_ChapterSoftmaxTemperatureMonotone
import Theorems.Thm_BookProof_ChapterSoftmaxTemperatureMonotone_scoreSoftmax_antitone_of_min
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
    (i : Fin m) (hmin : ∀ l, s i ≤ s l) :
    scoreSoftmax gamma s i ≤ scoreSoftmax beta s i := scoreSoftmax_antitone_of_min s i hmin hbg
