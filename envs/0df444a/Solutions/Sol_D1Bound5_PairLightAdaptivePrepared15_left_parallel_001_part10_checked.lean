-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.left_parallel_001_part10_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:27:26.462998+00:00
-- url     : https://prove2.me/submissions/61054f19-f717-47af-a85a-79040fbf60ae

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

/-- Original heads 212 through 213, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 2
      (PairLightPrepared15.leftCached.drop 212) (PairLightPrepared15.leftRows.drop 212) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared15
end
