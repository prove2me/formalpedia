-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ggDet_keyM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:43:12.399707+00:00
-- url     : https://prove2.me/submissions/0f6133b7-65b2-4e3c-85b5-aace5c1e392f

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds
import Theorems.Thm_Formalism_QuantumDeterminants_ggDet_swapBlocks
import Theorems.Thm_Formalism_QuantumDeterminants_ggDet_keyN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution (n : ℕ) (Z W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (α β : ℂ) :
    (fromBlocks (α • ggLastU n) Z W (β • ggLastU n)).det =
      (-1) ^ (n + 1) * (Z.det * W.det - α * β * (Z.submatrix Fin.castSucc Fin.castSucc).det *
        (W.submatrix Fin.castSucc Fin.castSucc).det) := by
  have h : fromBlocks (α • ggLastU n) Z W (β • ggLastU n) * fromBlocks 0 (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) 1 0 =
      fromBlocks Z (α • ggLastU n) (β • ggLastU n) W := by
    simp [fromBlocks_multiply]
  have h' := congrArg Matrix.det h
  rw [det_mul, ggDet_swapBlocks, ggDet_keyN] at h'
  have hs : ((-1 : ℂ) ^ (n + 1)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
  linear_combination ((-1 : ℂ) ^ (n + 1)) * h' - (fromBlocks (α • ggLastU n) Z W (β • ggLastU n)).det * hs
end Formalism.QuantumDeterminants
