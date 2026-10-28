-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.right_parallel_002_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:25:17.021979+00:00
-- url     : https://prove2.me/submissions/873043b0-8c61-461b-b5aa-e4f72101dc61

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 214 through 225, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.rightCached.drop 214) (PairLightPrepared14.rightRows.drop 214) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared14
end
