-- Prove2me | solution 1 for Formalism.SLP.Final.submoduleCountDed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:47:39.051383+00:00
-- url     : https://prove2.me/submissions/9a6b2843-6336-4470-ab96-3fd180c37792

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CardEqCardRangeNsmulMulCardKer
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SesquilinearDeterminantHolds
import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_OmegaPow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DedekindLFunctions
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Theorems.Thm_Formalism_SLP_P_card_submodules_le_of_dedekind


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
theorem _root_.solution : Formalism.SLP.SubmoduleCountDed := Formalism.SLP.P.card_submodules_le_of_dedekind
end Formalism.SLP.Final
