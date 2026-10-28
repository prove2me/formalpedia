-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_prefix_000_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:24:05.440983+00:00
-- url     : https://prove2.me/submissions/32620e73-9239-4bdd-8fc5-b5076e67b1c2

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

/-- Original heads 52 through 62, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 11
      (PairLightPrepared6.leftCached.drop 52)
      (PairLightPrepared6.leftRows.drop 52) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
