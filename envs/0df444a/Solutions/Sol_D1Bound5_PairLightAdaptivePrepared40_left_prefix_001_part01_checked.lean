-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared40.left_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:34:14.969748+00:00
-- url     : https://prove2.me/submissions/bc07ca1f-4cc2-4601-8999-6ee8be9f46ca

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 187 through 259; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 73
      (leftCached001.drop 50) (leftRows001.drop 50) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared40
end
