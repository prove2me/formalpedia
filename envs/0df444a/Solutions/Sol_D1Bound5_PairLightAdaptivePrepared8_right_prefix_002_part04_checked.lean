-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_002_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:10:31.269761+00:00
-- url     : https://prove2.me/submissions/e80ce2ae-d5af-4aa3-b0fa-43465529c823

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

/-- Original heads 167 through 178, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 12
      (PairLightPrepared8.rightCached.drop 167)
      (PairLightPrepared8.rightRows.drop 167) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
