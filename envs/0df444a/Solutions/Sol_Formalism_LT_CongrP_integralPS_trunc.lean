-- Prove2me | solution 1 for Formalism.LT.CongrP.integralPS_trunc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:33:52.356555+00:00
-- url     : https://prove2.me/submissions/0c83053f-bc1a-40f4-9221-5b3420bdb8ee

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow

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
theorem _root_.solution {a : PowerSeries K} (ha : IntegralPS a) (M : ℕ) :
    IntegralPS (trunc M a : PowerSeries K) := fun n => by
  rw [Polynomial.coeff_coe, coeff_trunc]
  split_ifs
  · exact ha n
  · simp
end Formalism.LT.CongrP
