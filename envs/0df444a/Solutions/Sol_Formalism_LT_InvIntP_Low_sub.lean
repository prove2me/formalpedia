-- Prove2me | solution 1 for Formalism.LT.InvIntP.Low.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:45.686181+00:00
-- url     : https://prove2.me/submissions/f9e740c6-3902-4aa2-ba4e-a2b673af647c

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
theorem _root_.solution {m : ℕ} {x y : MvPowerSeries ι K} (hx : Low m x) (hy : Low m y) :
    Low m (x - y) := by
  intro d hd
  rw [map_sub, hx d hd, hy d hd, sub_zero]
end Low
end Formalism.LT.InvIntP
