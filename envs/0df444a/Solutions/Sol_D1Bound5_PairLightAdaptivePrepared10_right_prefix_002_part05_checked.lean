-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.right_prefix_002_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:09:41.952992+00:00
-- url     : https://prove2.me/submissions/f9a228fe-a2e3-4565-baa9-fe5b12abfd6e

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 236 through 254, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 19
      (PairLightPrepared10.rightCached.drop 236)
      (PairLightPrepared10.rightRows.drop 236) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
