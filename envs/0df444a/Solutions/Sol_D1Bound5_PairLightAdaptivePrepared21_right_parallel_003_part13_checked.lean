-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.right_parallel_003_part13_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:44.186908+00:00
-- url     : https://prove2.me/submissions/e65fb4be-0495-4d74-9f49-527c8acbb10c

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 491 through 502, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.rightCached.drop 491) (PairLightPrepared21.rightRows.drop 491) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared21
end
