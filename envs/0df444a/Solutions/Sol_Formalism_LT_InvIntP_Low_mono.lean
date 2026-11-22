-- Prove2me | solution 1 for Formalism.LT.InvIntP.Low.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:00:10.277863+00:00
-- url     : https://prove2.me/submissions/383d1958-5e88-4a11-9429-69f383e48545

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
namespace Low
theorem _root_.solution {m k : ℕ} {x : MvPowerSeries ι K} (h : Low m x) (hk : k ≤ m) : Low k x := by
  exact fun d hd => h d (lt_of_lt_of_le hd hk)
end Low
end Formalism.LT.InvIntP
