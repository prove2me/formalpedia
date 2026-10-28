-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_003_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:51.417779+00:00
-- url     : https://prove2.me/submissions/b5edd5b9-50f3-4378-b768-c1b2d9b76303

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

/-- Original heads 260 through 273, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 14
      (PairLightPrepared8.rightCached.drop 260)
      (PairLightPrepared8.rightRows.drop 260) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
