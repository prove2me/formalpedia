-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.nearTotalAbs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:18:08.670834+00:00
-- url     : https://prove2.me/submissions/29aba526-fa98-4213-ab96-98e9d9c4095b

import Definitions.Def_Formalism_FlagUnipotentLattices_CuspidalityThreshold
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_OperatorHilbertSchmidtNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_CuspThresholdBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_near_region_total_abs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.Final Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts
namespace Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.NearTotalAbs := Formalism.HermitianLatticeCounting.P.near_region_total_abs
end Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts
