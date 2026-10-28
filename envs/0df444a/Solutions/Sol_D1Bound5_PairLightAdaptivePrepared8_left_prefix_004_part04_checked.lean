-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_004_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:24.378999+00:00
-- url     : https://prove2.me/submissions/0c768e34-de7a-4c64-a93f-073f80d50f7b

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

/-- Original heads 339 through 356, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 18
      (PairLightPrepared8.leftCached.drop 339)
      (PairLightPrepared8.leftRows.drop 339) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
