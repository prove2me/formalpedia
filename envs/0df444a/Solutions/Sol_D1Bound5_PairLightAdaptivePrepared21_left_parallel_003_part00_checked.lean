-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.left_parallel_003_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:48:03.90812+00:00
-- url     : https://prove2.me/submissions/29c0ae92-835a-448f-af65-22bcd8fd3c7c

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

/-- Original heads 335 through 346, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 335) (PairLightPrepared21.leftRows.drop 335) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared21
end
