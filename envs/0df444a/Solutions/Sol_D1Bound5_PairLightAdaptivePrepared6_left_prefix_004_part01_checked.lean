-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_prefix_004_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:36.743127+00:00
-- url     : https://prove2.me/submissions/eb6a14a9-6c2b-4baf-a0f2-38225d6ed4be

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

/-- Original heads 338 through 358, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 21
      (PairLightPrepared6.leftCached.drop 338)
      (PairLightPrepared6.leftRows.drop 338) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
