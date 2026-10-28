-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_003_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:05:47.882987+00:00
-- url     : https://prove2.me/submissions/55911149-1cc6-4bd4-b1d1-60d85e70fda1

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

/-- Original heads 260 through 273, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 14
      (PairLightPrepared8.leftCached.drop 260)
      (PairLightPrepared8.leftRows.drop 260) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
