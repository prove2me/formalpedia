-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_007_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:45:55.604551+00:00
-- url     : https://prove2.me/submissions/ddfc3e78-cd6b-49fc-94fa-cf14d781fab3

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 628 through 639; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 12
      (leftCached007.drop 12) (leftRows007.drop 12) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
