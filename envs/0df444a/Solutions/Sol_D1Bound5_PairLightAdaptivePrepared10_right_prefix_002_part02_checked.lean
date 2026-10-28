-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.right_prefix_002_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:30:25.867925+00:00
-- url     : https://prove2.me/submissions/8b6fec3a-195c-40fa-84c8-ef989670b1b5

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

/-- Original heads 184 through 200, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 17
      (PairLightPrepared10.rightCached.drop 184)
      (PairLightPrepared10.rightRows.drop 184) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
