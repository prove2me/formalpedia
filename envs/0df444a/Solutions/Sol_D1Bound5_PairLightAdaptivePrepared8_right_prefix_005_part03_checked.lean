-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_005_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:45:29.016931+00:00
-- url     : https://prove2.me/submissions/530f023b-7123-44ac-a4cb-30414a00dcd0

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

/-- Original heads 439 through 463, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 25
      (PairLightPrepared8.rightCached.drop 439)
      (PairLightPrepared8.rightRows.drop 439) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
