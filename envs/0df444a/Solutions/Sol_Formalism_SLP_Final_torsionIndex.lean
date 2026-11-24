-- Prove2me | solution 1 for Formalism.SLP.Final.torsionIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:01:30.336073+00:00
-- url     : https://prove2.me/submissions/ea760174-3313-42ee-a522-d1d0e60ae908

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CardEqCardRangeNsmulMulCardKer
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SesquilinearDeterminantHolds
import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_OmegaPow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DedekindLFunctions
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Theorems.Thm_Formalism_SLP_P_card_range_nsmul_mul_card_le


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
theorem _root_.solution : Formalism.SLP.TorsionIndex := Formalism.SLP.P.card_range_nsmul_mul_card_le
end Formalism.SLP.Final
