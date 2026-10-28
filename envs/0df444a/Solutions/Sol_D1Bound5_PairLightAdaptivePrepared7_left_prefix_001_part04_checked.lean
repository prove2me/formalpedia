-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.left_prefix_001_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:25:29.133396+00:00
-- url     : https://prove2.me/submissions/f33eb038-3ad3-4e09-bd28-0fb5d8c700c3

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 201 through 224, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.leftCached.drop 201)
      (PairLightPrepared7.leftRows.drop 201) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared7
end
