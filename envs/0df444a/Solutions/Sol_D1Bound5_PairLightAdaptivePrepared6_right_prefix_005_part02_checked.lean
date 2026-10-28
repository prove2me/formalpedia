-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.right_prefix_005_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:35:32.043591+00:00
-- url     : https://prove2.me/submissions/d97fd18d-afa2-4221-9417-6ff0f7430364

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

/-- Original heads 563 through 637, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 75
      (PairLightPrepared6.rightCached.drop 563)
      (PairLightPrepared6.rightRows.drop 563) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
