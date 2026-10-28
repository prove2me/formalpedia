-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_002_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:29:47.740478+00:00
-- url     : https://prove2.me/submissions/367202a0-5044-47b5-a5bd-77a5f9525772

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 189 through 202, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 14
      (PairLightPrepared6.rightCached.drop 189)
      (PairLightPrepared6.rightRows.drop 189) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
