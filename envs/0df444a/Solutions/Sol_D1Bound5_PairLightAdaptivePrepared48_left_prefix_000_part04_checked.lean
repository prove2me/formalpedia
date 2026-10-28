-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared48.left_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:22:01.0572+00:00
-- url     : https://prove2.me/submissions/0c314419-754d-45c1-8617-c6fa884d127b

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 134 through 136; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 3
      (leftCached000.drop 134) (leftRows000.drop 134) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared48
end
