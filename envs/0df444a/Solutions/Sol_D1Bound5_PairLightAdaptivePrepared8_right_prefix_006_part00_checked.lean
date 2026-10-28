-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_006_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:01:14.392674+00:00
-- url     : https://prove2.me/submissions/d5f0ad68-6bf7-44f6-81f1-c92cd3ae12af

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 524 through 559, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 36
      (PairLightPrepared8.rightCached.drop 524)
      (PairLightPrepared8.rightRows.drop 524) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
