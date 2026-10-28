-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_005_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:10.391067+00:00
-- url     : https://prove2.me/submissions/30b40d21-b3e6-4257-ad34-5298a6cd8fda

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

/-- Original heads 375 through 394, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 20
      (PairLightPrepared8.rightCached.drop 375)
      (PairLightPrepared8.rightRows.drop 375) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
