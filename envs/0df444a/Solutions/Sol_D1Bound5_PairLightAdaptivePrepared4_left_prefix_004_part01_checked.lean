-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.left_prefix_004_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:31:53.402023+00:00
-- url     : https://prove2.me/submissions/dfc7e77f-c6ba-4ffb-aef2-036ef899f14b

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 441 through 485, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 45
      (PairLightPrepared4.leftCached.drop 441)
      (PairLightPrepared4.leftRows.drop 441) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
