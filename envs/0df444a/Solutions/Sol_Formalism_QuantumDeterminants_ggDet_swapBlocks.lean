-- Prove2me | solution 1 for Formalism.QuantumDeterminants.ggDet_swapBlocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:12:40.782387+00:00
-- url     : https://prove2.me/submissions/ce216010-4399-4567-aacc-c167b92bd908

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_ReverseCauchySchwarzHolds

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
theorem _root_.solution (m : ℕ) :
    (fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) 1 0).det = (-1) ^ m := by
  have h : fromBlocks (0 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) (0 : Matrix (Fin m) (Fin m) ℂ) =
      fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) (0 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) * fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) (-(1 : Matrix (Fin m) (Fin m) ℂ)) (0 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) *
        fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) (0 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) (1 : Matrix (Fin m) (Fin m) ℂ) * fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) (0 : Matrix (Fin m) (Fin m) ℂ) (0 : Matrix (Fin m) (Fin m) ℂ) (-(1 : Matrix (Fin m) (Fin m) ℂ)) := by
    simp [fromBlocks_multiply]
  rw [h]
  simp [det_mul, det_neg]
end Formalism.QuantumDeterminants
