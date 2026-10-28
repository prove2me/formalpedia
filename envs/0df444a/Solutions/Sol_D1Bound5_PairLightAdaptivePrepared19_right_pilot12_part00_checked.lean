-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.right_pilot12_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:49:01.42967+00:00
-- url     : https://prove2.me/submissions/a8594eb7-ed3e-4916-85cd-20a038f63500

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

/-- Original heads 0 through 11, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 12
      (PairLightPrepared19.rightCached.drop 0)
      (PairLightPrepared19.rightRows.drop 0) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared19
end
