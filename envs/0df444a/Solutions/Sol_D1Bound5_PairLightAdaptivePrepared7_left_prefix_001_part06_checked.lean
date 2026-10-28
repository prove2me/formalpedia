-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.left_prefix_001_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:38:29.273004+00:00
-- url     : https://prove2.me/submissions/d22a16cf-477f-4a8b-bd46-5cf95264b776

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

/-- Original heads 249 through 267, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 19
      (PairLightPrepared7.leftCached.drop 249)
      (PairLightPrepared7.leftRows.drop 249) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared7
end
