-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_003_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:52:57.047969+00:00
-- url     : https://prove2.me/submissions/7563c93f-5029-43ef-96c8-6b5907b4521b

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 249 through 265, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 17
      (PairLightPrepared6.rightCached.drop 249)
      (PairLightPrepared6.rightRows.drop 249) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
