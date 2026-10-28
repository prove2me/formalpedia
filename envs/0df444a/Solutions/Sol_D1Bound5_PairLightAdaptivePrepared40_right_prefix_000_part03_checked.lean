-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared40.right_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:39:02.703708+00:00
-- url     : https://prove2.me/submissions/092cd801-b815-4969-8f18-799d7d34c12c

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 96 through 136; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 41
      (rightCached000.drop 96) (rightRows000.drop 96) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared40
end
