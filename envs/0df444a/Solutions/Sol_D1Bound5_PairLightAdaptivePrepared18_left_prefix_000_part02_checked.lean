-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared18.left_prefix_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:33.767359+00:00
-- url     : https://prove2.me/submissions/959997ae-55ff-4846-b580-1fa81a6f25d7

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData18_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData18_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared18
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 77 through 130; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared18.sieve 54
      (leftCached000.drop 77) (leftRows000.drop 77) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared18
end
