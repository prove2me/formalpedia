-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared48.right_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:52.225627+00:00
-- url     : https://prove2.me/submissions/5eaa0df5-c04e-4470-9a45-c29298d9c88f

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 265 through 357; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 93
      (rightCached001.drop 127) (rightRows001.drop 127) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared48
end
