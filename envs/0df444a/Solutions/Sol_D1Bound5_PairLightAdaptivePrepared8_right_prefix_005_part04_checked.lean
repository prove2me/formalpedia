-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_005_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:30.250308+00:00
-- url     : https://prove2.me/submissions/f77b8552-e847-46f1-a3cf-e4ae3984d9af

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

/-- Original heads 464 through 490, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 27
      (PairLightPrepared8.rightCached.drop 464)
      (PairLightPrepared8.rightRows.drop 464) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
