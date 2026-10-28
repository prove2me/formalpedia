-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared29.right_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:17:11.956891+00:00
-- url     : https://prove2.me/submissions/bb12120f-b472-4041-bd16-54f64c32a001

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 78 through 108, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 31
      (rightCached000.drop 78) (rightRows000.drop 78) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared29
end
