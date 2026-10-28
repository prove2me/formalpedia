-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.left_parallel_001_part08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:52:49.345034+00:00
-- url     : https://prove2.me/submissions/54c9a2e7-c1b5-4e85-a406-c15ed29a43dd

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

/-- Original heads 184 through 195, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 184) (PairLightPrepared14.leftRows.drop 184) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared14
end
