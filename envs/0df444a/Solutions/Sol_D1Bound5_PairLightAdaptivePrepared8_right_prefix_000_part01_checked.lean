-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:37:34.615492+00:00
-- url     : https://prove2.me/submissions/d049f215-f327-441a-9236-c3de7b48b63b

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

/-- Original heads 9 through 17, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 9
      (PairLightPrepared8.rightCached.drop 9)
      (PairLightPrepared8.rightRows.drop 9) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
