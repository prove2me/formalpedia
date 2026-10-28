-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_006_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:21:47.609179+00:00
-- url     : https://prove2.me/submissions/c5bcecf2-a6ed-4bd7-be82-807020ac9656

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

/-- Original heads 665 through 717, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 53
      (PairLightPrepared8.rightCached.drop 665)
      (PairLightPrepared8.rightRows.drop 665) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
