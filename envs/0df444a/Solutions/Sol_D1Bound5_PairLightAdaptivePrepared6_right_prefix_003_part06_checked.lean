-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_003_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:30:17.091268+00:00
-- url     : https://prove2.me/submissions/cc423180-592a-4c39-aff4-23e7e7d726ad

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 320 through 320, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 1
      (PairLightPrepared6.rightCached.drop 320)
      (PairLightPrepared6.rightRows.drop 320) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
