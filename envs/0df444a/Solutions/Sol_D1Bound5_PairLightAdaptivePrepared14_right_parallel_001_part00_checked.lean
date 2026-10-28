-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.right_parallel_001_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:42:15.998965+00:00
-- url     : https://prove2.me/submissions/f5f6b5c5-8a15-455d-bbe7-7b0fa1347c0e

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 88 through 99, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 88) (PairLightPrepared14.rightRows.drop 88) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared14
end
