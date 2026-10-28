-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared1.left_prefix_001_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:46:18.93755+00:00
-- url     : https://prove2.me/submissions/6e5c0b58-a265-4f1b-9ba7-76e2fb274114

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 269 through 359, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 91
      (leftCached001.drop 132) (leftRows001.drop 132) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared1
end
