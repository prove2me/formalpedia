-- Prove2me | solution 1 for Formalism.LT.InvIntP.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:33:56.730905+00:00
-- url     : https://prove2.me/submissions/7718474a-3fba-4792-838a-70a360c1f408

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt

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
universe u v
open Formalism Formalism.LT Formalism.LT.InvIntP
open Formalism.G Formalism.G.LogCR
variable {K : Type u} [NormedField K] {ι : Type v}
namespace Formalism.LT.InvIntP
theorem _root_.solution (f : PowerSeries K) (h0 : constantCoeff f = 0) (h1 : coeff 1 f = 1) :
    f = X + X ^ 2 * tail2 f := by
  ext n
  rcases n with _ | _ | n <;>
    simp [tail2, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X, h0, h1]
end Formalism.LT.InvIntP
