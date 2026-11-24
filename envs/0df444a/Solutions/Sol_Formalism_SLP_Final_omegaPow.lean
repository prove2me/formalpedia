-- Prove2me | solution 1 for Formalism.SLP.Final.omegaPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:05:27.522206+00:00
-- url     : https://prove2.me/submissions/fac78d10-82ba-48c5-8684-72256d7e42e9

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CardEqCardRangeNsmulMulCardKer
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SesquilinearDeterminantHolds
import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SubgroupCount
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_OmegaPow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DedekindLFunctions
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Theorems.Thm_Formalism_SLP_P_pow_primeFactors_length_le


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
theorem _root_.solution : Formalism.SLP.OmegaPow := Formalism.SLP.P.pow_primeFactors_length_le
end Formalism.SLP.Final
