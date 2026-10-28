-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.right_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:48:10.963719+00:00
-- url     : https://prove2.me/submissions/51fb6b0f-5793-4467-9ee0-f7f91a306304

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

/-- Original heads 84 through 96, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 13
      (PairLightPrepared10.rightCached.drop 84)
      (PairLightPrepared10.rightRows.drop 84) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
