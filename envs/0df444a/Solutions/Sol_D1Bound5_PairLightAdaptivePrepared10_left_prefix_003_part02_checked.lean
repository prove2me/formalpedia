-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_prefix_003_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:20:04.434207+00:00
-- url     : https://prove2.me/submissions/bf361ddd-1365-4046-a382-2cfd9f4a079e

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

/-- Original heads 296 through 318, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 23
      (PairLightPrepared10.leftCached.drop 296)
      (PairLightPrepared10.leftRows.drop 296) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
