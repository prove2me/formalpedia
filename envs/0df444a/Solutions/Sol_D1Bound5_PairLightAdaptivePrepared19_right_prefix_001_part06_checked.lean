-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.right_prefix_001_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:42:23.52777+00:00
-- url     : https://prove2.me/submissions/4bda67f8-1107-456e-82f4-d5d0c6a66490

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

/-- Original heads 245 through 247, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 3
      (PairLightPrepared19.rightCached.drop 245)
      (PairLightPrepared19.rightRows.drop 245) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared19
end
