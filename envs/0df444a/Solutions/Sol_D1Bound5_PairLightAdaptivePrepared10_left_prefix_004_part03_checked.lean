-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_prefix_004_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:35:54.297138+00:00
-- url     : https://prove2.me/submissions/8784ee8a-82d8-444e-b254-297a18959d29

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

/-- Original heads 550 through 595, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 46
      (PairLightPrepared10.leftCached.drop 550)
      (PairLightPrepared10.leftRows.drop 550) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
