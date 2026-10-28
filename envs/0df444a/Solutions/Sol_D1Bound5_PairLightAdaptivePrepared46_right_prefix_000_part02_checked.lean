-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared46.right_prefix_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:33:21.169745+00:00
-- url     : https://prove2.me/submissions/92c8eb45-a176-439a-ab03-9bf6370306cd

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 36 through 57, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 22
      (rightCached000.drop 36) (rightRows000.drop 36) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared46
end
