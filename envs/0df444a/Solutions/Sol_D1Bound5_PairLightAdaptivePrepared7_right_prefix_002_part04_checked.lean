-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.right_prefix_002_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:53:13.100197+00:00
-- url     : https://prove2.me/submissions/0573e374-86e1-4b3d-9dbf-3e0d31c4f688

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 368 through 391, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.rightCached.drop 368)
      (PairLightPrepared7.rightRows.drop 368) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared7
end
