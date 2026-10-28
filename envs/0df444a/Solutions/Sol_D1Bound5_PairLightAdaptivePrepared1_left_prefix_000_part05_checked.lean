-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared1.left_prefix_000_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:16:26.042314+00:00
-- url     : https://prove2.me/submissions/9619e529-648e-4dea-8b3e-3d3c9f5b01df

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 108 through 136, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 29
      (leftCached000.drop 108) (leftRows000.drop 108) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared1
end
