-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared23.right_parallel_001_part10_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:53:22.783003+00:00
-- url     : https://prove2.me/submissions/07710f6b-d726-42a4-ad4c-de21cf35c279

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

/-- Original heads 212 through 213, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 2
      (PairLightPrepared23.rightCached.drop 212) (PairLightPrepared23.rightRows.drop 212) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared23
end
