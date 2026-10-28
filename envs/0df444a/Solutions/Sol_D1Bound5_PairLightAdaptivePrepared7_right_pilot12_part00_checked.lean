-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.right_pilot12_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:12:38.662994+00:00
-- url     : https://prove2.me/submissions/e0a46bac-34bd-43ec-8f7d-c6981c081f0e

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 0 through 11, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 12
      (PairLightPrepared7.rightCached.drop 0)
      (PairLightPrepared7.rightRows.drop 0) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared7
end
