-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.threshCuspOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:37:26.806715+00:00
-- url     : https://prove2.me/submissions/16217d09-23aa-4132-ab2f-e8c70d81510c

import Definitions.Def_Formalism_FlagUnipotentLattices_CuspidalityThreshold
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_OperatorHilbertSchmidtNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_CuspThresholdBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_threshold_cusp_operator


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.ThreshCuspOp := Formalism.HermitianLatticeCounting.P.threshold_cusp_operator
end Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts
