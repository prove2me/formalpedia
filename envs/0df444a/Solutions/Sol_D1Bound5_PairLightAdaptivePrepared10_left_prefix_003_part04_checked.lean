-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_prefix_003_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:45:35.874154+00:00
-- url     : https://prove2.me/submissions/93771ac5-a6b2-461b-987b-ad83e4d42528

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

/-- Original heads 344 through 370, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 27
      (PairLightPrepared10.leftCached.drop 344)
      (PairLightPrepared10.leftRows.drop 344) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
