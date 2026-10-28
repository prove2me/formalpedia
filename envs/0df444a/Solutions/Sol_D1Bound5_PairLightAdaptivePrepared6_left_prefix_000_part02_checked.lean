-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_prefix_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:00.778901+00:00
-- url     : https://prove2.me/submissions/56584aa2-2da1-4706-8691-13c9027204ad

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 20 through 29, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 10
      (PairLightPrepared6.leftCached.drop 20)
      (PairLightPrepared6.leftRows.drop 20) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
