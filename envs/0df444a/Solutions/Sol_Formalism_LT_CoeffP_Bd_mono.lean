-- Prove2me | solution 1 for Formalism.LT.CoeffP.Bd.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:12:15.695772+00:00
-- url     : https://prove2.me/submissions/70fc8fa9-3557-4d18-a9b9-d36e5495f508

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne

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
open Formalism Formalism.LT Formalism.LT.CoeffP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {ι : Type v}
namespace Formalism.LT.CoeffP
namespace Bd
theorem _root_.solution {a b : ℝ} {F : MvPowerSeries ι K} (hF : Bd a F) (h : a ≤ b) : Bd b F := by
  intro d
  exact (hF d).trans h
end Bd
end Formalism.LT.CoeffP
