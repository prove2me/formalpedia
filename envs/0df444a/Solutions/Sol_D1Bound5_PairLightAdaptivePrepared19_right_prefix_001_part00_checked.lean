-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.right_prefix_001_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:32.926423+00:00
-- url     : https://prove2.me/submissions/6a88aa86-3545-4f08-af50-0aaf8b0160cd

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

/-- Original heads 101 through 124, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.rightCached.drop 101)
      (PairLightPrepared19.rightRows.drop 101) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared19
end
