-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared23.right_parallel_002_part12_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:06:22.530992+00:00
-- url     : https://prove2.me/submissions/0e3a52ed-1953-410e-a6fd-a2ea09192fbe

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 358 through 369, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 358) (PairLightPrepared23.rightRows.drop 358) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared23
end
