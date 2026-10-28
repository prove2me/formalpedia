-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.right_prefix_002_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:28:25.938636+00:00
-- url     : https://prove2.me/submissions/47f9c0cb-ad6b-4fef-aedf-eaa3ded1b558

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

/-- Original heads 218 through 235, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 18
      (PairLightPrepared10.rightCached.drop 218)
      (PairLightPrepared10.rightRows.drop 218) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
