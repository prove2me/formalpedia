-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_003_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:19:39.600819+00:00
-- url     : https://prove2.me/submissions/b9f5caac-9abb-4240-948c-8317c415363b

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

/-- Original heads 233 through 248, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 16
      (PairLightPrepared6.rightCached.drop 233)
      (PairLightPrepared6.rightRows.drop 233) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
