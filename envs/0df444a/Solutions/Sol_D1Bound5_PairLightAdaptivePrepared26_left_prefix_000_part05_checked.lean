-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_000_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:58:49.293088+00:00
-- url     : https://prove2.me/submissions/be9f275a-e7af-4c7c-a7b1-9d42c6bcebec

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 15 through 17 of the original first block; every full tail is retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached000.drop 15) (leftRows000.drop 15) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
