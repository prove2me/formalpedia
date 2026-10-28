-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_004_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:31:54.189012+00:00
-- url     : https://prove2.me/submissions/8661e1ae-b8ed-4abf-afb4-af8b7e990e25

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

/-- Original heads 386 through 410, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 25
      (PairLightPrepared6.rightCached.drop 386)
      (PairLightPrepared6.rightRows.drop 386) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
