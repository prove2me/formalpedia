-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared17.right_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:46:22.290554+00:00
-- url     : https://prove2.me/submissions/3cc3838b-4786-4b67-80ec-69b44ba9b129

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 189 through 264; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 76
      (rightCached001.drop 51) (rightRows001.drop 51) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared17
end
