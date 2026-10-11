-- Prove2me | solution 1 for BookProof.ChapterScaledDotProduct.scoreSoftmax_scaled
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:30:50.41585+00:00
-- url     : https://prove2.me/submissions/dca30f35-2568-4f57-9327-dfebd050370f

-- Generated from ChapterScaledDotProduct.lean — solution of BookProof.ChapterScaledDotProduct.scoreSoftmax_scaled
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
import Theorems.Thm_BookProof_ChapterScaledDotProduct_scoreSoftmax_div
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterScaledDotProduct



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

variable {d : ℕ}
variable {m : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    scoreSoftmax beta (fun l => s l / Real.sqrt d) j
      = scoreSoftmax (beta / Real.sqrt d) s j := scoreSoftmax_div beta (Real.sqrt d) s j
