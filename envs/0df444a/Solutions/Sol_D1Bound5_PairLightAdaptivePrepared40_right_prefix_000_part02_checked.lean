-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared40.right_prefix_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T06:13:51.387934+00:00
-- url     : https://prove2.me/submissions/d143e98a-83d3-439f-9bed-7777485b7bc3

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 61 through 95; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 35
      (rightCached000.drop 61) (rightRows000.drop 61) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared40
end
