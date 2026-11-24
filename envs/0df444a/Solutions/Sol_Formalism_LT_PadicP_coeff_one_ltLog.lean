-- Prove2me | solution 1 for Formalism.LT.PadicP.coeff_one_ltLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:33:43.757317+00:00
-- url     : https://prove2.me/submissions/7c86eb01-6e15-489b-b80f-7c9226a70067

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul
import Theorems.Thm_Formalism_LT_PadicP_coeff_ltLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.LT Formalism.LT.PadicP
open Formalism.G
variable {p : ℕ} [hp : Fact p.Prime]
namespace Formalism.LT.PadicP
theorem _root_.solution : coeff 1 (ltLog p) = 1 := by
  rw [coeff_ltLog, if_pos ⟨0, pow_zero p⟩, Nat.cast_one, inv_one]
end Formalism.LT.PadicP
