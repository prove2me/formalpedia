-- Prove2me | solution 1 for Formalism.LT.PadicP.constantCoeff_ltLog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:33:45.191031+00:00
-- url     : https://prove2.me/submissions/ddefbb01-1f76-4812-8bc4-e118e0198586

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
theorem _root_.solution : constantCoeff (ltLog p) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_ltLog, if_neg]
  rintro ⟨k, hk⟩
  exact absurd hk (pow_ne_zero k hp.out.ne_zero)
end Formalism.LT.PadicP
