-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_003_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:34.062713+00:00
-- url     : https://prove2.me/submissions/a81c64ab-6956-47e9-ae1b-4ee962ce7a6c

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 246 through 259, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 14
      (PairLightPrepared8.rightCached.drop 246)
      (PairLightPrepared8.rightRows.drop 246) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
