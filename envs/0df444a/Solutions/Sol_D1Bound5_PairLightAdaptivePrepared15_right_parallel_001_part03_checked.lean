-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared15.right_parallel_001_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:20:45.958644+00:00
-- url     : https://prove2.me/submissions/9b692eb5-9f82-42f8-9c91-ac441b3b7cfc

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

/-- Original heads 128 through 139, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared15.sieve 12
      (PairLightPrepared15.rightCached.drop 128) (PairLightPrepared15.rightRows.drop 128) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared15
end
