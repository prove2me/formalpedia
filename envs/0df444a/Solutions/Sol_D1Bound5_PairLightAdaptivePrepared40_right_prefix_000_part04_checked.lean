-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared40.right_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:35:29.724895+00:00
-- url     : https://prove2.me/submissions/1382aad1-fc4d-4e40-9dc5-cead8196050d

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 137 through 137; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 1
      (rightCached000.drop 137) (rightRows000.drop 137) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared40
end
