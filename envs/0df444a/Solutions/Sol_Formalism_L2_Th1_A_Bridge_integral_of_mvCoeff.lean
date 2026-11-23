-- Prove2me | solution 1 for Formalism.L2.Th1.A.Bridge.integral_of_mvCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:22:25.071808+00:00
-- url     : https://prove2.me/submissions/a1411a6b-9eee-40dd-8d80-e3a50b39d777

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
theorem _root_.solution {ι : Type} {f : MvPowerSeries ι K}
    (h : ∀ n, MvPowerSeries.coeff n f ∈ Formalism.G.unitBall K) : Formalism.DworkPowerSeriesWeights.Integral f := by
  unfold Formalism.DworkPowerSeriesWeights.Integral
  intro n
  exact h n
end Formalism.L2.Th1.A.Bridge
