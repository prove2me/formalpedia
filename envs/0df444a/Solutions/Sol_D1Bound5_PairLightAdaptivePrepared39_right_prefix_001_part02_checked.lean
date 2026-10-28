-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared39.right_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:18:17.57122+00:00
-- url     : https://prove2.me/submissions/0ae2c01a-cb3c-42fb-8e03-b59dd0bccf35

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

/-- Original heads 146 through 169, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared39.sieve 24
      (PairLightPrepared39.rightCached.drop 146)
      (PairLightPrepared39.rightRows.drop 146) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared39
end
