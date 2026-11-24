-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.deepChainV
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:34:19.781917+00:00
-- url     : https://prove2.me/submissions/b26dca05-3668-493c-bb22-79a16c8ee650

import Definitions.Def_Formalism_FlagUnipotentLattices_CuspidalityThreshold
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_OperatorHilbertSchmidtNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_CuspThresholdBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_deep_region_chain_volume


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.DeepChainV := Formalism.HermitianLatticeCounting.P.deep_region_chain_volume
end Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts
