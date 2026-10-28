-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.right_prefix_003_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:39:40.486663+00:00
-- url     : https://prove2.me/submissions/cd219bda-2399-4ba5-97d6-9c0896a2e37a

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

/-- Original heads 275 through 295, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 21
      (PairLightPrepared10.rightCached.drop 275)
      (PairLightPrepared10.rightRows.drop 275) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
