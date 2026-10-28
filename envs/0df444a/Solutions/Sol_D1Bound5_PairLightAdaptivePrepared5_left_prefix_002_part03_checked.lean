-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.left_prefix_002_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:41:45.649122+00:00
-- url     : https://prove2.me/submissions/8ff3e602-32b6-4cbb-9f1b-a002f788caa6

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData5Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 341 through 364, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 24
      (PairLightPrepared5.leftCached.drop 341)
      (PairLightPrepared5.leftRows.drop 341) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared5
end
