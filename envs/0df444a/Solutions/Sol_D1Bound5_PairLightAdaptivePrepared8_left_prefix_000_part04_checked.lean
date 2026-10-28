-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:35.210809+00:00
-- url     : https://prove2.me/submissions/cfad9ab5-b763-43f3-a26f-3a2346a45c6c

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 38 through 47, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 10
      (PairLightPrepared8.leftCached.drop 38)
      (PairLightPrepared8.leftRows.drop 38) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
