-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.left_parallel_003_part12_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:17:04.87427+00:00
-- url     : https://prove2.me/submissions/aa5a3651-b334-47eb-aa46-9e5c955bd682

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 479 through 490, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 479) (PairLightPrepared21.leftRows.drop 479) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared21
end
