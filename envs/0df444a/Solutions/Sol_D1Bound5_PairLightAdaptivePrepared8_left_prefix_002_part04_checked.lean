-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_002_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:51:21.928988+00:00
-- url     : https://prove2.me/submissions/206b4482-b067-48fd-816e-84c3b45953e5

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 168 through 179, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 12
      (PairLightPrepared8.leftCached.drop 168)
      (PairLightPrepared8.leftRows.drop 168) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
