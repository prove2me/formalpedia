-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_prefix_005_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:24:16.942309+00:00
-- url     : https://prove2.me/submissions/d80f14d2-9e66-4140-8ecc-82d26c9c9228

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

/-- Original heads 506 through 551, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 46
      (PairLightPrepared6.leftCached.drop 506)
      (PairLightPrepared6.leftRows.drop 506) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
