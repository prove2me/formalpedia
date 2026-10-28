-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_000_part15_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:25:27.270411+00:00
-- url     : https://prove2.me/submissions/fa9ea827-c466-4a71-a6cd-40170f5194f8

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 45 through 47 of the original first block; every full tail is retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached000.drop 45) (leftRows000.drop 45) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
