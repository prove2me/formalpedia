-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.cusp_threshold_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:18:07.443801+00:00
-- url     : https://prove2.me/submissions/30e565d7-176d-4c85-9672-a9850e62224a

import Definitions.Def_Formalism_FlagUnipotentLattices_CuspidalityThreshold
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_OperatorHilbertSchmidtNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_CuspThresholdBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_threshold_cusp_numeric


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.CuspidalityThreshold := Formalism.HermitianLatticeCounting.P.threshold_cusp_numeric
end Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts
