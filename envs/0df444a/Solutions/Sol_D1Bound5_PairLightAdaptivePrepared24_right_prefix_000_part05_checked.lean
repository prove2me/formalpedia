-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared24.right_prefix_000_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:20:50.223662+00:00
-- url     : https://prove2.me/submissions/ce0b7d0a-b951-435d-be90-0b02f194e980

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 60 through 71, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 12
      (PairLightPrepared24.rightCached.drop 60)
      (PairLightPrepared24.rightRows.drop 60) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared24
end
