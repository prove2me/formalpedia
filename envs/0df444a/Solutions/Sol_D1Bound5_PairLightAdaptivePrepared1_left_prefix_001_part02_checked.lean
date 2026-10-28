-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared1.left_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:03.889736+00:00
-- url     : https://prove2.me/submissions/5736e821-4276-4873-b457-d765a8911abb

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 213 through 268, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 56
      (leftCached001.drop 76) (leftRows001.drop 76) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared1
end
