-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.left_parallel_002_part13_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:44:24.005018+00:00
-- url     : https://prove2.me/submissions/e179ddc7-4586-4e56-86f6-81b67bcee6d6

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

/-- Original heads 358 through 369, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 12
      (PairLightPrepared14.leftCached.drop 358) (PairLightPrepared14.leftRows.drop 358) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared14
end
