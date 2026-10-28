-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_005_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:35:34.039177+00:00
-- url     : https://prove2.me/submissions/7380e6a0-6e7d-4171-83eb-099ca6417f60

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

/-- Original heads 417 through 439, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 23
      (PairLightPrepared8.leftCached.drop 417)
      (PairLightPrepared8.leftRows.drop 417) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
