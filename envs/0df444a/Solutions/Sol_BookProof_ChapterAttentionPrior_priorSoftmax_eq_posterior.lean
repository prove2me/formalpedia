-- Prove2me | solution 1 for BookProof.ChapterAttentionPrior.priorSoftmax_eq_posterior
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T20:37:41.314975+00:00
-- url     : https://prove2.me/submissions/a613a62a-79ef-4a04-a4f1-c29447448f8f

import Mathlib
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Definitions.Def_ChapterAttentionPrior
import Definitions.Def_ChapterBayesInference

set_option autoImplicit false
set_option linter.all false

open BookProof BookProof.ChapterAttentionPrior in open BookProof.ChapterBayesInference in open BookProof.ChapterAttentionPrior in open scoped BigOperators in open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder in
theorem solution {m : ℕ} (w : Fin m → ℝ) (beta : ℝ) (s : Fin m → ℝ) (j : Fin m) :
    priorSoftmax w beta s j
      = posterior w (fun l (_ : Unit) => Real.exp (beta * s l)) () j := by
  intros
  rfl
