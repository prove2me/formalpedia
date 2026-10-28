-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared1.left_prefix_000_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:30.335618+00:00
-- url     : https://prove2.me/submissions/c0a7f542-6671-458b-bcfa-e6695fa885b9

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 0 through 15, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 16
      (leftCached000.drop 0) (leftRows000.drop 0) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared1
end
