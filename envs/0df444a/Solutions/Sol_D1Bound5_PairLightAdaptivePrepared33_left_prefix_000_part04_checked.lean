-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared33.left_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:17.270909+00:00
-- url     : https://prove2.me/submissions/6075fdb6-db33-4b83-b762-216a1f20113d

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData33_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 134 through 136; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 3
      (leftCached000.drop 134) (leftRows000.drop 134) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared33
end
