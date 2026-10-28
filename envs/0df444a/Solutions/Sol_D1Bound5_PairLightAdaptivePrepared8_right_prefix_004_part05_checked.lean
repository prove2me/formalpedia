-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_004_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:13:29.609993+00:00
-- url     : https://prove2.me/submissions/bc4fa09d-ae2b-4368-8f9d-5d6e4e434c3f

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

/-- Original heads 356 through 374, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 19
      (PairLightPrepared8.rightCached.drop 356)
      (PairLightPrepared8.rightRows.drop 356) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
