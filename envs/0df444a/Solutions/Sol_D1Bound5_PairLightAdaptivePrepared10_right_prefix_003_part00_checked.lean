-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.right_prefix_003_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:43:52.290803+00:00
-- url     : https://prove2.me/submissions/2570ea43-1f20-4fef-bb0d-d7af6fbda821

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

/-- Original heads 255 through 274, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 20
      (PairLightPrepared10.rightCached.drop 255)
      (PairLightPrepared10.rightRows.drop 255) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
