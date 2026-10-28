-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_prefix_003_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:25:16.066988+00:00
-- url     : https://prove2.me/submissions/41391ad1-77d8-4c57-8ac2-82893e7c11f9

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 264 through 280, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 17
      (PairLightPrepared6.leftCached.drop 264)
      (PairLightPrepared6.leftRows.drop 264) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
