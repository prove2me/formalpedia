-- Prove2me | solution 1 for Formalism.LIFT.lift_WBTail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:15:50.416226+00:00
-- url     : https://prove2.me/submissions/e2842a32-06f9-4d45-bc36-afce9c182afc

import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_LagrangeIdeal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_LagrangeIdealCyc
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_Graded
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CompsOfMemMap
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UChase
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_CoeffSumXPowMulExpand
import Definitions.Def_Formalism_LagrangeIdealLifts_LiftLagrangeIdealInt
import Theorems.Thm_Formalism_LIFT_gammaGradedStep_holds
import Theorems.Thm_Formalism_LIFT_lagrangeIdealCyc_of
import Theorems.Thm_Formalism_LIFT_lagrangian_ideal_holds
import Theorems.Thm_Formalism_LIFT_wBTail_of


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
theorem _root_.solution : WBTail := wBTail_of gammaGradedStep_holds (lagrangeIdealCyc_of lagrangian_ideal_holds)
end Formalism.LIFT
