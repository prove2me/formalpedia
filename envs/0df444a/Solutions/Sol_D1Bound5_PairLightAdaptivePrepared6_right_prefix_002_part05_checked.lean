-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_002_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:17.886573+00:00
-- url     : https://prove2.me/submissions/8d3d6266-977b-47cd-868f-50c9c75baccb

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

/-- Original heads 203 through 217, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 15
      (PairLightPrepared6.rightCached.drop 203)
      (PairLightPrepared6.rightRows.drop 203) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
