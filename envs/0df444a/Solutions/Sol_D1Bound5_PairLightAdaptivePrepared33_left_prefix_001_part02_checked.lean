-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared33.left_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:30.16436+00:00
-- url     : https://prove2.me/submissions/75d010a3-bd69-4a0c-908c-929c02263079

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData33_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 260 through 359; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 100
      (leftCached001.drop 123) (leftRows001.drop 123) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared33
end
