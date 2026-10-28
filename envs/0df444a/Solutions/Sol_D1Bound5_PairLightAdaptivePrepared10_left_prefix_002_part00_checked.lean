-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_prefix_002_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:27:16.073194+00:00
-- url     : https://prove2.me/submissions/07ee682d-3463-40bf-85bf-648be5279e1e

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 153 through 167, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 15
      (PairLightPrepared10.leftCached.drop 153)
      (PairLightPrepared10.leftRows.drop 153) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
