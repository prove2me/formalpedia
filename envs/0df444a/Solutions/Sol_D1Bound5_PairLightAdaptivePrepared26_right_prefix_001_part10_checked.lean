-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.right_prefix_001_part10_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:45:28.540509+00:00
-- url     : https://prove2.me/submissions/deab6653-7bdd-4af5-861b-7a370491d607

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 84 through 86; all later vertices retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (rightCached001.drop 30) (rightRows001.drop 30) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
