-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_prefix_002_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:18:33.58589+00:00
-- url     : https://prove2.me/submissions/d9a68733-55cb-4ada-b85d-df2f50f7e63d

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData10Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared10
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 168 through 183, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 16
      (PairLightPrepared10.leftCached.drop 168)
      (PairLightPrepared10.leftRows.drop 168) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
