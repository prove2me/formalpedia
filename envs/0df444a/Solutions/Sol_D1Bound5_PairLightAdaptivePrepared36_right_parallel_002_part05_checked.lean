-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.right_parallel_002_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:33:41.610679+00:00
-- url     : https://prove2.me/submissions/fccf9e7b-b9ad-43ae-84b5-81d806043d29

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

/-- Original heads 227 through 238, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.rightCached.drop 227) (PairLightPrepared36.rightRows.drop 227) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared36
end
