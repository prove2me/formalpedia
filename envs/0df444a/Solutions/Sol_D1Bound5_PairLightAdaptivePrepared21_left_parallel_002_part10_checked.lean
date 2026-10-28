-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.left_parallel_002_part10_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:16.465172+00:00
-- url     : https://prove2.me/submissions/ee5743ca-1e35-4c9e-b05f-fd3d467dcccb

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 304 through 315, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 304) (PairLightPrepared21.leftRows.drop 304) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared21
end
