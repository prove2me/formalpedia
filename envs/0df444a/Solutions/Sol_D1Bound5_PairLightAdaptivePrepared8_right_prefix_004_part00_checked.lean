-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_004_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:54:48.264895+00:00
-- url     : https://prove2.me/submissions/9d88c859-79cb-46ea-93b2-d1cc10e43a5e

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

/-- Original heads 274 through 288, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 15
      (PairLightPrepared8.rightCached.drop 274)
      (PairLightPrepared8.rightRows.drop 274) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
