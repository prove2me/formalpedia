-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared46.left_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:44:31.927999+00:00
-- url     : https://prove2.me/submissions/3d44ae9e-b7dd-4ac3-85d1-63fe5875d6a8

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 213 through 268, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 56
      (leftCached001.drop 76) (leftRows001.drop 76) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared46
end
