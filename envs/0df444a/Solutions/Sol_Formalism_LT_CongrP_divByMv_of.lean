-- Prove2me | solution 1 for Formalism.LT.CongrP.divByMv_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:33:47.709952+00:00
-- url     : https://prove2.me/submissions/6d0967db-f80f-48c8-9b48-937176123919

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow
import Theorems.Thm_Formalism_LT_CongrP_mv_coeff_eq

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
universe u
open Formalism Formalism.LT Formalism.LT.CongrP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.CongrP
theorem _root_.solution (x : K) (φ : PowerSeries K) (h : DivBy x φ) : DivByMv x φ := fun d => by
  rw [mv_coeff_eq]; exact h _
end Formalism.LT.CongrP
