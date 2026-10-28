-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.right_prefix_002_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:40:22.62298+00:00
-- url     : https://prove2.me/submissions/c6f6dee8-73cd-4955-813f-07ca4a3d1fa0

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 168 through 183, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 16
      (PairLightPrepared10.rightCached.drop 168)
      (PairLightPrepared10.rightRows.drop 168) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
