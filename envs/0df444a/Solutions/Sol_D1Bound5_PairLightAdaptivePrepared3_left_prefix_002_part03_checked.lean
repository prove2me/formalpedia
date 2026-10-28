-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared3.left_prefix_002_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:22:17.597499+00:00
-- url     : https://prove2.me/submissions/21125e5f-8a1b-40a5-a1ab-04011b19bd4f

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 383 through 406, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 24
      (PairLightPrepared3.leftCached.drop 383)
      (PairLightPrepared3.leftRows.drop 383) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared3
end
