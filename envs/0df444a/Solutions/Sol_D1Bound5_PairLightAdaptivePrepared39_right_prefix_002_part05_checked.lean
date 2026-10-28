-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared39.right_prefix_002_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:23.285134+00:00
-- url     : https://prove2.me/submissions/aed4321e-64eb-47f0-8212-dd077b407fbd

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData39Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared39
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 356 through 379, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.rightCached.drop 356)
      (PairLightPrepared39.rightRows.drop 356) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared39
end
