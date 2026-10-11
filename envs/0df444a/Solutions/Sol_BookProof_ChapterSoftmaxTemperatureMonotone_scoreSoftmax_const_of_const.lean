-- Prove2me | solution 1 for BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_const_of_const
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:45:15.042983+00:00
-- url     : https://prove2.me/submissions/6fc621bd-7634-43fa-8080-cae7db2992b9

-- Generated from ChapterSoftmaxTemperatureMonotone.lean — solution of BookProof.ChapterSoftmaxTemperatureMonotone.scoreSoftmax_const_of_const
import Mathlib
import Definitions.Def_ChapterSoftmaxTemperatureMonotone
import Theorems.Thm_BookProof_ChapterSoftmaxOrder_scoreSoftmax_const
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterSoftmaxTemperatureMonotone



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m : ℕ}

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {s : Fin m → ℝ} {c : ℝ} (hs : ∀ l, s l = c)
    (beta : ℝ) (j : Fin m) : scoreSoftmax beta s j = 1 / (m : ℝ) := by

  have hfun : s = fun _ => c := funext hs
  subst hfun
  exact scoreSoftmax_const beta c j
