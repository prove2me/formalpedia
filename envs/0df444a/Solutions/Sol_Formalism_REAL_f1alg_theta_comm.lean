-- Prove2me | solution 1 for Formalism.REAL.f1alg_theta_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:44:05.207314+00:00
-- url     : https://prove2.me/submissions/e833b460-6ef7-479a-a3a4-fc33c174a81b

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Theorems.Thm_Formalism_REAL_f1alg_theta_mul

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (X Y : Matrix (Fin n) (Fin n) ℂ) :
    Jm ε * (X * Y - Y * X) * Jm ε =
      (Jm ε * X * Jm ε) * (Jm ε * Y * Jm ε) - (Jm ε * Y * Jm ε) * (Jm ε * X * Jm ε) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, f1alg_theta_mul, f1alg_theta_mul]
end Formalism.REAL
