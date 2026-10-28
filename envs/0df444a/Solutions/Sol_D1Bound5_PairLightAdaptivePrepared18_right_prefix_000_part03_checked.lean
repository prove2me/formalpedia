-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared18.right_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:33:34.12199+00:00
-- url     : https://prove2.me/submissions/81049302-5e45-4f26-8d18-8d70e29e5e85

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData18_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 131 through 261; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 131
      (rightCached000.drop 131) (rightRows000.drop 131) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared18
end
