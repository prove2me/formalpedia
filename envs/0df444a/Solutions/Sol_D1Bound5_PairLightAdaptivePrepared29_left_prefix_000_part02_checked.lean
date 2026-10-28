-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared29.left_prefix_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:39:01.815039+00:00
-- url     : https://prove2.me/submissions/c5d5be0b-71d8-46c5-8b8d-a4f18a5b5a5f

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData29_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 50 through 77, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared29.sieve 28
      (leftCached000.drop 50) (leftRows000.drop 50) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared29
end
