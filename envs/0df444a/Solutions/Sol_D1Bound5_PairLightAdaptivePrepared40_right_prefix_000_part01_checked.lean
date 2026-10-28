-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared40.right_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:18:53.313431+00:00
-- url     : https://prove2.me/submissions/f2ed505e-06e0-4f76-880d-355fe5facfd8

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 29 through 60; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 32
      (rightCached000.drop 29) (rightRows000.drop 29) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared40
end
