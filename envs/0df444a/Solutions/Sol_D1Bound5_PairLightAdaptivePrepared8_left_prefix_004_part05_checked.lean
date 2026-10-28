-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.left_prefix_004_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:52.874681+00:00
-- url     : https://prove2.me/submissions/61a49b69-b5a3-43fe-9e6d-855155f66e7d

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

/-- Original heads 357 through 375, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 19
      (PairLightPrepared8.leftCached.drop 357)
      (PairLightPrepared8.leftRows.drop 357) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
