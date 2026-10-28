-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_prefix_003_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:39:39.704422+00:00
-- url     : https://prove2.me/submissions/d85c8fc8-48ff-48d9-a474-e16425b97210

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

/-- Original heads 299 through 317, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 19
      (PairLightPrepared6.leftCached.drop 299)
      (PairLightPrepared6.leftRows.drop 299) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
