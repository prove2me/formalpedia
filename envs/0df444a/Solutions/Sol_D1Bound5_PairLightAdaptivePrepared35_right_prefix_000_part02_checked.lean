-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared35.right_prefix_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:27.730733+00:00
-- url     : https://prove2.me/submissions/f42bb9ac-7247-44b4-a2a1-e4d8e4f4363a

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 58 through 91; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 34
      (rightCached000.drop 58) (rightRows000.drop 58) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared35
end
