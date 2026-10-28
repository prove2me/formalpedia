-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.right_parallel_002_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:43:30.230163+00:00
-- url     : https://prove2.me/submissions/aa8e4d06-7cb9-4235-9c7b-6b3a4e0055ea

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

/-- Original heads 239 through 250, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 239) (PairLightPrepared36.rightRows.drop 239) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared36
end
