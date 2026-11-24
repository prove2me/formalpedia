-- Prove2me | solution 1 for Formalism.REAL.f1alg_theta_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:34:46.084005+00:00
-- url     : https://prove2.me/submissions/284be6c7-db92-4200-8957-b36e8d55fce7

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Theorems.Thm_Formalism_REAL_f1alg_JJ_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (A B : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (A * B) * Jm ε = (Jm ε * A * Jm ε) * (Jm ε * B * Jm ε) := by
  simp only [Matrix.mul_assoc, f1alg_JJ_left]
end Formalism.REAL
