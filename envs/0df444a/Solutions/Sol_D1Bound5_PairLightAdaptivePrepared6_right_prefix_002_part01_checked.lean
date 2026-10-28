-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_002_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:51:21.046462+00:00
-- url     : https://prove2.me/submissions/b7ae2c8a-a435-4407-a3f0-b5dcef9fa952

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

/-- Original heads 148 through 160, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 13
      (PairLightPrepared6.rightCached.drop 148)
      (PairLightPrepared6.rightRows.drop 148) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
