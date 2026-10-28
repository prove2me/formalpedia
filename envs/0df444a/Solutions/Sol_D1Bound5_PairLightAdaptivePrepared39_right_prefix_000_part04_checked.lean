-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared39.right_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:18:20.091362+00:00
-- url     : https://prove2.me/submissions/cc9f64b4-4b2d-4c14-a43d-a08b21bada2d

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

/-- Original heads 48 through 59, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 12
      (PairLightPrepared39.rightCached.drop 48)
      (PairLightPrepared39.rightRows.drop 48) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared39
end
