-- Prove2me | solution 1 for Formalism.L2.Th1.E.XTShape_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:38:07.769752+00:00
-- url     : https://prove2.me/submissions/a8f574d0-dc08-4880-86d8-8ec05647aa97

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementT
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_TwoTorsionU
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SeriesSubgroup
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInvTDen
import Theorems.Thm_UpperTheory_Reformulated_B_SeriesSubgroup_XTShape_holds


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
open Shape
namespace Formalism.L2.Th1.E
theorem _root_.solution : XTShape := UpperTheory.Reformulated.B.SeriesSubgroup.XTShape_holds
end Formalism.L2.Th1.E
