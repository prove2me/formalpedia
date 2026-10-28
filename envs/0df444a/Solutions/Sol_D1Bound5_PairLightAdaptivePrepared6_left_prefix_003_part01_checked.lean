-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_prefix_003_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:52:55.389601+00:00
-- url     : https://prove2.me/submissions/50e648fa-79cd-4014-a123-1ff04f2747c1

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

/-- Original heads 231 through 246, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 16
      (PairLightPrepared6.leftCached.drop 231)
      (PairLightPrepared6.leftRows.drop 231) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
