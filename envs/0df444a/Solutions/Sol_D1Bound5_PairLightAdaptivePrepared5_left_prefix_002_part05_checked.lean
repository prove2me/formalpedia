-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared5.left_prefix_002_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:49:18.926659+00:00
-- url     : https://prove2.me/submissions/fbff5f48-3d71-41d8-9622-ef44883dfdbe

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

/-- Original heads 389 through 412, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared5.sieve 24
      (PairLightPrepared5.leftCached.drop 389)
      (PairLightPrepared5.leftRows.drop 389) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared5
end
