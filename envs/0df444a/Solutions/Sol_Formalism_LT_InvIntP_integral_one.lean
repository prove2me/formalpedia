-- Prove2me | solution 1 for Formalism.LT.InvIntP.integral_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:45.78985+00:00
-- url     : https://prove2.me/submissions/4e73bd65-aa10-4591-af2b-c48a5947c8a1

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
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}
namespace Formalism.LT.InvIntP
theorem _root_.solution : IntegralMv (1 : MvPowerSeries ι K) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp
end Formalism.LT.InvIntP
