-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_005_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:35.628273+00:00
-- url     : https://prove2.me/submissions/5f78eec6-5fa9-4612-bef0-b0ac76614ed1

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

/-- Original heads 521 through 523, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 3
      (PairLightPrepared8.rightCached.drop 521)
      (PairLightPrepared8.rightRows.drop 521) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
