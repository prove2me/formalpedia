-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.right_prefix_002_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:53:11.028654+00:00
-- url     : https://prove2.me/submissions/744b8f42-3852-4dd5-8c02-3880d713c5cb

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 368 through 391, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 24
      (PairLightPrepared5.rightCached.drop 368)
      (PairLightPrepared5.rightRows.drop 368) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared5
end
