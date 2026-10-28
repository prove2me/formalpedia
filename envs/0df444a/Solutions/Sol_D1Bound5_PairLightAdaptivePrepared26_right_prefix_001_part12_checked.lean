-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_001_part12_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:23:39.208175+00:00
-- url     : https://prove2.me/submissions/dc54f118-6691-42f6-89c7-c18d7f66513d

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 90 through 92; all later vertices retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached001.drop 36) (rightRows001.drop 36) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
