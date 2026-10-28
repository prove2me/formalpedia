-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_002_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:00.327244+00:00
-- url     : https://prove2.me/submissions/62f1cc70-f99a-4679-be82-f8be863f2e74

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 144 through 155, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 12
      (PairLightPrepared8.leftCached.drop 144)
      (PairLightPrepared8.leftRows.drop 144) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
