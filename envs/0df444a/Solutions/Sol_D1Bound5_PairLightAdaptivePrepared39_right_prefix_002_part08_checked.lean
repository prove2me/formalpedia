-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared39.right_prefix_002_part08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:45:50.68043+00:00
-- url     : https://prove2.me/submissions/c85a6d0d-85ad-4a2a-bd74-99f488378f5b

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

/-- Original heads 428 through 451, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.rightCached.drop 428)
      (PairLightPrepared39.rightRows.drop 428) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared39
end
