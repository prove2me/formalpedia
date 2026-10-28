-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_005_part08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:23.236982+00:00
-- url     : https://prove2.me/submissions/57e7690c-4297-4e6d-adb4-35ecfcdba3f0

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 432 through 442; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 11
      (leftCached005.drop 96) (leftRows005.drop 96) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
