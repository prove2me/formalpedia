-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:32:39.028961+00:00
-- url     : https://prove2.me/submissions/1f46b905-8e63-41ca-898e-461439c72593

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

/-- Original heads 11 through 21, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 11
      (PairLightPrepared10.leftCached.drop 11)
      (PairLightPrepared10.leftRows.drop 11) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
