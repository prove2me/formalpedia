-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_001_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:37.589555+00:00
-- url     : https://prove2.me/submissions/d795051a-b332-407d-9c0f-298368e2c2ec

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

/-- Original heads 123 through 134, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 12
      (PairLightPrepared6.rightCached.drop 123)
      (PairLightPrepared6.rightRows.drop 123) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
