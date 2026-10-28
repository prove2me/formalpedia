-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.right_prefix_001_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:23:27.727767+00:00
-- url     : https://prove2.me/submissions/cedcd87a-7160-4d8c-ad64-fab1f2d9755e

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

/-- Original heads 197 through 220, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.rightCached.drop 197)
      (PairLightPrepared19.rightRows.drop 197) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared19
end
