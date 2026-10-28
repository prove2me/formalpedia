-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_prefix_001_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:50:48.598985+00:00
-- url     : https://prove2.me/submissions/05e53e37-f8ac-4eba-bab2-54902e47c329

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

/-- Original heads 122 through 133, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 12
      (PairLightPrepared6.leftCached.drop 122)
      (PairLightPrepared6.leftRows.drop 122) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
