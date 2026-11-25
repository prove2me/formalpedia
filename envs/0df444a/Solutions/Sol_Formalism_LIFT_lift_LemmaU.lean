-- Prove2me | solution 1 for Formalism.LIFT.lift_LemmaU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:27:05.96131+00:00
-- url     : https://prove2.me/submissions/1a523494-e575-46cd-ae6f-425df68d0bbb

import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_LagrangeIdeal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_LagrangeIdealCyc
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_Graded
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CompsOfMemMap
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UChase
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CoeffSumXPowMulExpand
import Definitions.Def_Formalism_LagrangeIdealLifts_LiftLagrangeIdealInt
import Theorems.Thm_Formalism_LIFT_gammaGradedStep_holds
import Theorems.Thm_Formalism_LIFT_lemmaU_of
import Theorems.Thm_Formalism_LIFT_uChase_proof
import Theorems.Thm_Formalism_LIFT_uClaim_of
import Theorems.Thm_Formalism_LIFT_uGraded_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LIFT
namespace Formalism.LIFT
theorem _root_.solution : LemmaU := lemmaU_of (uClaim_of (uGraded_of gammaGradedStep_holds) gammaGradedStep_holds) uChase_proof
end Formalism.LIFT
