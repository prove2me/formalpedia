-- Prove2me | solution 1 for BookProof.TensorSumChain.posEsaOp_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:53:56.880719+00:00
-- url     : https://prove2.me/submissions/034b1d8a-7ad6-4e4a-85b2-9f8c4084643b

import Definitions.Def_ChapterTensorSumChain

open scoped TensorProduct
open BookProof.FarisLavine BookProof.TensorCore BookProof.TensorSumChain

noncomputable section

theorem solution :
    ¬ ∃ C : ℝ, ∀ x : posEsaOp.dom,
      ‖posEsaOp.op x‖ ≤ C * ‖(x : posEsaOp.space.carrier)‖ := by
  exact BookProof.TensorSumEsa.positionCube_first_not_bounded
