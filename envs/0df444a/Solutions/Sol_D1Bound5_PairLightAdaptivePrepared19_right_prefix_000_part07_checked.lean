-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.right_prefix_000_part07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:08:37.475583+00:00
-- url     : https://prove2.me/submissions/1e521de3-d305-4ca7-adb6-83f3d910921e

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 84 through 95, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 12
      (PairLightPrepared19.rightCached.drop 84)
      (PairLightPrepared19.rightRows.drop 84) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared19
end
