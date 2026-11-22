-- Prove2me | solution 1 for Formalism.LT.InvIntP.low_of_agree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:00:53.822231+00:00
-- url     : https://prove2.me/submissions/bd63a147-c9bb-428b-8892-6e6fae73c3d0

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
theorem _root_.solution {N : ℕ} {a b : MvPowerSeries ι K} (hab : Agree N a b) : Low N (a - b) := by
  intro d hd
  rw [map_sub, hab d hd, sub_self]
end Formalism.LT.InvIntP
