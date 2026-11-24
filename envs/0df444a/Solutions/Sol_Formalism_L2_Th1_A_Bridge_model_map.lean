-- Prove2me | solution 1 for Formalism.L2.Th1.A.Bridge.model_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:19:36.484916+00:00
-- url     : https://prove2.me/submissions/6ba33e4a-b61e-4dc1-bae4-5f425ad1969f

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
theorem _root_.solution (W : WeierstrassCurve K) (h : IntModel W) :
    (model W h).map (Formalism.G.unitBall K).subtype = W := by
  rfl
end Formalism.L2.Th1.A.Bridge
