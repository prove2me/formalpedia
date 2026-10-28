-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.right_parallel_003_part00_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:57:27.243725+00:00
-- url     : https://prove2.me/submissions/f1849b21-eeac-4a2d-babb-3f2e54b4398f

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 287 through 298, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 287) (PairLightPrepared36.rightRows.drop 287) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared36
end
