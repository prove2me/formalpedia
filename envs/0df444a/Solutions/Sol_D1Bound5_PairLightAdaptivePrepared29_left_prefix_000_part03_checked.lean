-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared29.left_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:56:48.714161+00:00
-- url     : https://prove2.me/submissions/b94ee9ec-2f44-46d5-882a-26e04c71b170

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
      (leftCached000.drop 78) (leftRows000.drop 78) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared29
end
