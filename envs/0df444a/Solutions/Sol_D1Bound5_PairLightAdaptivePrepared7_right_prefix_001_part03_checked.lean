-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.right_prefix_001_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:27.836004+00:00
-- url     : https://prove2.me/submissions/eb7f0695-8972-41a0-bcab-f03ef7ba2d5f

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

/-- Original heads 178 through 201, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.rightCached.drop 178)
      (PairLightPrepared7.rightRows.drop 178) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared7
end
