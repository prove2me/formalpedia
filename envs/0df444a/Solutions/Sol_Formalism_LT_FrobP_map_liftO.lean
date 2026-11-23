-- Prove2me | solution 1 for Formalism.LT.FrobP.map_liftO
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:38:24.943843+00:00
-- url     : https://prove2.me/submissions/654cfeae-894f-49c7-8788-7ea5ee86c8c4

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open Formalism Formalism.LT Formalism.LT.FrobP
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.LT.FrobP
theorem _root_.solution {ι : Type v} (A : MvPowerSeries ι K) (hA : IntegralMv A) :
    MvPowerSeries.map (unitBall K).subtype (liftO A hA) = A := by
  ext d
  rw [MvPowerSeries.coeff_map]
  rfl
end Formalism.LT.FrobP
