-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.left_parallel_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:44:04.009539+00:00
-- url     : https://prove2.me/submissions/9321f4cc-4ed3-43f5-90a8-3eb6787dc069

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 24 through 35, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.leftCached.drop 24) (PairLightPrepared15.leftRows.drop 24) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared15
end
