-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared23.right_parallel_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:08:02.570988+00:00
-- url     : https://prove2.me/submissions/5dca48b3-ff67-485a-a355-8bf9759112ad

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

/-- Original heads 12 through 23, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.rightCached.drop 12) (PairLightPrepared23.rightRows.drop 12) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared23
end
