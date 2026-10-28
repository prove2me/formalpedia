-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared35.right_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:15.621365+00:00
-- url     : https://prove2.me/submissions/031609a6-4843-44d8-96c9-62f10fb154b7

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 28 through 57; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 30
      (rightCached000.drop 28) (rightRows000.drop 28) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared35
end
