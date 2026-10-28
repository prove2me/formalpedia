-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_prefix_004_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:53:48.831599+00:00
-- url     : https://prove2.me/submissions/6dc02999-3f49-4713-bbdc-8b7a58fd8fe8

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

/-- Original heads 441 through 485, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 45
      (PairLightPrepared10.leftCached.drop 441)
      (PairLightPrepared10.leftRows.drop 441) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
