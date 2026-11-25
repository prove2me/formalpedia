-- Prove2me | solution 1 for Formalism.L2.Th1.E.Shape.mem_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:44:58.157808+00:00
-- url     : https://prove2.me/submissions/8adbb865-94ca-4c6e-a639-646c16249761

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_TwoTorsionU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SeriesSubgroup
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInvTDen

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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Shape
namespace Formalism.L2.Th1.E.Shape
theorem _root_.solution {K : Type} [NormedField K] [IsUltrametricDist K] {a : K} :
    a ∈ ball K ↔ ‖a‖ ≤ 1 := Iff.rfl
end Formalism.L2.Th1.E.Shape
