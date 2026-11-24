-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts.cubeMult
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:22:14.520024+00:00
-- url     : https://prove2.me/submissions/e7a3ad17-0c2e-438c-811d-bc4335ad9f80

import Definitions.Def_Formalism_FlagUnipotentLattices_CuspidalityThreshold
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_OperatorHilbertSchmidtNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_CuspThresholdBound
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_cube_multiplication


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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S7.CubeMult := Formalism.HermitianLatticeCounting.P.cube_multiplication
end Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts
