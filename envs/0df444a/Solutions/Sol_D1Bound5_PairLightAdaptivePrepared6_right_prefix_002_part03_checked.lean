-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_002_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:31:02.756989+00:00
-- url     : https://prove2.me/submissions/871c8c9c-12cd-4226-bfe4-549ffb18c0ef

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

/-- Original heads 175 through 188, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 14
      (PairLightPrepared6.rightCached.drop 175)
      (PairLightPrepared6.rightRows.drop 175) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
