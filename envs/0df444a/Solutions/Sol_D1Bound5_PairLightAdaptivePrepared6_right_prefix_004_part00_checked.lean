-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_004_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:12:20.777993+00:00
-- url     : https://prove2.me/submissions/ff5b1326-b87b-4c16-b808-687bcebae08d

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

/-- Original heads 321 through 340, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 20
      (PairLightPrepared6.rightCached.drop 321)
      (PairLightPrepared6.rightRows.drop 321) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
