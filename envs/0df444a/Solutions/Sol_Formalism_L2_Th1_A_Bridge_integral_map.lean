-- Prove2me | solution 1 for Formalism.L2.Th1.A.Bridge.integral_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:19:35.676044+00:00
-- url     : https://prove2.me/submissions/02d7b903-fd13-4254-b8d5-fcd3fb8f4ca2

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementJ
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_BridgeJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open Formalism.L2.Th1.A.Bridge
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.L2.Th1.A.Bridge
theorem _root_.solution {ι : Type} (c : MvPowerSeries ι (Formalism.G.unitBall K)) :
    Formalism.DworkPowerSeriesWeights.Integral (MvPowerSeries.map (Formalism.G.unitBall K).subtype c) := by
  unfold Formalism.DworkPowerSeriesWeights.Integral
  intro n
  rw [MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff n c).2
end Formalism.L2.Th1.A.Bridge
