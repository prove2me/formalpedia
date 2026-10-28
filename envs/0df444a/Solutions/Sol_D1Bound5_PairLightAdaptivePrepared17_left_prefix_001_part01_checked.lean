-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared17.left_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:20:18.909212+00:00
-- url     : https://prove2.me/submissions/d26d754c-4852-42d9-a6c7-659ee008dfe3

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 187 through 259; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 73
      (leftCached001.drop 50) (leftRows001.drop 50) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared17
end
