-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared33.right_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:27:41.528732+00:00
-- url     : https://prove2.me/submissions/22dc1ec2-cd5a-4781-b2ec-623149090b40

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData33_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 265 through 357; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 93
      (rightCached001.drop 127) (rightRows001.drop 127) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared33
end
