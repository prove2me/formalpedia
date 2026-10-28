-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_prefix_000_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:36:42.198728+00:00
-- url     : https://prove2.me/submissions/cca6f75a-0de7-4671-90dd-abeb0a4c99c2

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

/-- Original heads 58 through 70, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 13
      (PairLightPrepared10.leftCached.drop 58)
      (PairLightPrepared10.leftRows.drop 58) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
