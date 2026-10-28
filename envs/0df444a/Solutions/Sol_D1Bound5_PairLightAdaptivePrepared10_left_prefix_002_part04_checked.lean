-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared10.left_prefix_002_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:25:20.805999+00:00
-- url     : https://prove2.me/submissions/6c37f915-15d8-47dd-8625-9ae254680b5e

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

/-- Original heads 218 through 235, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared10.sieve 18
      (PairLightPrepared10.leftCached.drop 218)
      (PairLightPrepared10.leftRows.drop 218) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared10
end
