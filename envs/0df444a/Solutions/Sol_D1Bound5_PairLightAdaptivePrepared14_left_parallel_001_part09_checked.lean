-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.left_parallel_001_part09_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:51:28.010062+00:00
-- url     : https://prove2.me/submissions/f0903c56-017c-4b3d-95f7-a3727aa0fd42

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 196 through 201, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 6
      (PairLightPrepared14.leftCached.drop 196) (PairLightPrepared14.leftRows.drop 196) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared14
end
