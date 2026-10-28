-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_004_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:41.034408+00:00
-- url     : https://prove2.me/submissions/228b5f1b-c771-4b27-b1e9-e60d700213ff

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData8Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared8
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 338 through 355, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 18
      (PairLightPrepared8.rightCached.drop 338)
      (PairLightPrepared8.rightRows.drop 338) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
