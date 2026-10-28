-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_003_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:20.41899+00:00
-- url     : https://prove2.me/submissions/4a5f99f0-3cf5-473c-ab9d-b7a6f4574f2a

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

/-- Original heads 192 through 204, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 13
      (PairLightPrepared8.rightCached.drop 192)
      (PairLightPrepared8.rightRows.drop 192) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
