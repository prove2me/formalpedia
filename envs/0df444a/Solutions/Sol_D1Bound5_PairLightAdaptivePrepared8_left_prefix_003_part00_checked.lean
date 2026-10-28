-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_003_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:37:49.022146+00:00
-- url     : https://prove2.me/submissions/17144e65-bdae-48b1-b622-29686c82235b

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

/-- Original heads 192 through 204, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 13
      (PairLightPrepared8.leftCached.drop 192)
      (PairLightPrepared8.leftRows.drop 192) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
