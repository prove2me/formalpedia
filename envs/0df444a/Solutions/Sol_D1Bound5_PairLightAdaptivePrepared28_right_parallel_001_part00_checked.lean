-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.right_parallel_001_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:29.958846+00:00
-- url     : https://prove2.me/submissions/9bf4fae1-0900-4d3a-8355-f11d59c23f00

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 82 through 93, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 82) (PairLightPrepared28.rightRows.drop 82) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
