-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:24:30.084993+00:00
-- url     : https://prove2.me/submissions/1ff5dfe7-3249-4190-b59a-6fb0d7c2374f

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 78 through 87, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 10
      (PairLightPrepared8.leftCached.drop 78)
      (PairLightPrepared8.leftRows.drop 78) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
