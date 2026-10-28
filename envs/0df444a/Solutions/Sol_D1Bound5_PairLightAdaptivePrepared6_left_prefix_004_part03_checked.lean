-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared6.left_prefix_004_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:55:39.021614+00:00
-- url     : https://prove2.me/submissions/a58a242d-5432-49b3-96d0-0723561cf4da

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData6Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared6
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 382 through 406, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared6.sieve 25
      (PairLightPrepared6.leftCached.drop 382)
      (PairLightPrepared6.leftRows.drop 382) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared6
end
