-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_prefix_004_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:26:07.822761+00:00
-- url     : https://prove2.me/submissions/3ce11307-b6c4-4fd6-9e64-debe94f4858e

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

/-- Original heads 435 through 465, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 31
      (PairLightPrepared6.leftCached.drop 435)
      (PairLightPrepared6.leftRows.drop 435) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
