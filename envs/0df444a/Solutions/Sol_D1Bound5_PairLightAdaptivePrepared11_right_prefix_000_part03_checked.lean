-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared11.right_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:31:31.262049+00:00
-- url     : https://prove2.me/submissions/8d0701fb-4185-44a6-9e3f-aabe638eb854

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 58 through 81, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 24
      (rightCached000.drop 58) (rightRows000.drop 58) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared11
end
