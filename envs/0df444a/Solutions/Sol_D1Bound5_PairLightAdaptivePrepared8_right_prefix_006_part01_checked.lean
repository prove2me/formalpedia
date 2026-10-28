-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared8.right_prefix_006_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:42:21.479874+00:00
-- url     : https://prove2.me/submissions/95b75fa8-4a66-45ee-869c-ea8c6e1c6faa

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

/-- Original heads 560 through 603, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared8.sieve 44
      (PairLightPrepared8.rightCached.drop 560)
      (PairLightPrepared8.rightRows.drop 560) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared8
end
