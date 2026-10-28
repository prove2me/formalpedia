-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_005_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:22:02.080847+00:00
-- url     : https://prove2.me/submissions/2e8836c6-fd4a-4980-acee-66f41e9cb55d

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

/-- Original heads 491 through 520, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 30
      (PairLightPrepared8.rightCached.drop 491)
      (PairLightPrepared8.rightRows.drop 491) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
