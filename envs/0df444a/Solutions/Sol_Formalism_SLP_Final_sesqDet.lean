-- Prove2me | solution 1 for Formalism.SLP.Final.sesqDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:18:29.376608+00:00
-- url     : https://prove2.me/submissions/be533bfc-ce2c-4c7c-9405-e1d139850386

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CardEqCardRangeNsmulMulCardKer
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SesquilinearDeterminantHolds
import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_OmegaPow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DedekindLFunctions
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Theorems.Thm_Formalism_SLP_P_sesquilinear_determinant_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SLP Formalism.SLP.Final
namespace Formalism.SLP.Final
theorem _root_.solution : Formalism.SLP.SesqDet := Formalism.SLP.P.sesquilinear_determinant_holds
end Formalism.SLP.Final
