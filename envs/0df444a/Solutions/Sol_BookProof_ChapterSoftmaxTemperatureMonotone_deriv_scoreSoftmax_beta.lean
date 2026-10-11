-- Prove2me | solution 1 for BookProof.ChapterSoftmaxTemperatureMonotone.deriv_scoreSoftmax_beta
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:43:47.736164+00:00
-- url     : https://prove2.me/submissions/c6876f3c-6c13-4a90-8222-3ca296896580

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — solution of BookProof.ChapterSoftmaxTemperatureMonotone.deriv_scoreSoftmax_beta
import Mathlib
import Definitions.Def_ChapterSoftmaxTemperatureMonotone
import Theorems.Thm_BookProof_ChapterSoftmaxFluctuation_hasDerivAt_scoreSoftmax
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxFluctuation
open BookProof.ChapterSoftmaxTemperatureMonotone



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxFluctuation

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in

theorem solution (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    deriv (fun b : ℝ => scoreSoftmax b s j) beta
      = scoreSoftmax beta s j * (s j - meanScore beta s) :=
  (hasDerivAt_scoreSoftmax beta s j).deriv
