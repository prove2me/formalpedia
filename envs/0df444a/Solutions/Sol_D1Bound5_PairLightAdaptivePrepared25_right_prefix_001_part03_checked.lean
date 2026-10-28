-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared25.right_prefix_001_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:48:15.645779+00:00
-- url     : https://prove2.me/submissions/57e1dc15-dc03-4998-9752-8e29d331cd84

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData25_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData25Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 273 through 380, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared25.sieve 108
      (rightCached001.drop 148) (rightRows001.drop 148) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared25
end
