-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.right_parallel_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:33:17.99182+00:00
-- url     : https://prove2.me/submissions/24bfeb5c-3cd1-4d07-b2ea-0ac41c5c4141

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData15Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 12 through 23, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 12) (PairLightPrepared15.rightRows.drop 12) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared15
end
