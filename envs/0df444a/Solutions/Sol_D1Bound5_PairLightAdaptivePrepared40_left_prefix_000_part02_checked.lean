-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared40.left_prefix_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:51:54.474252+00:00
-- url     : https://prove2.me/submissions/31a1dfe9-c836-4685-9115-98f861b2cb1b

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 59 through 93; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 35
      (leftCached000.drop 59) (leftRows000.drop 59) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared40
end
