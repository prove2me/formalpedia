-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.left_prefix_000_part08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:10.759346+00:00
-- url     : https://prove2.me/submissions/536177f3-de6c-407e-991b-212afa56be44

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 96 through 104, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 9
      (PairLightPrepared5.leftCached.drop 96)
      (PairLightPrepared5.leftRows.drop 96) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared5
end
