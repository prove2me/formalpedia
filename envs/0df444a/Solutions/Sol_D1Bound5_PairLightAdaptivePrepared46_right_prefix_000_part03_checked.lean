-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared46.right_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:44:07.607832+00:00
-- url     : https://prove2.me/submissions/49308ea9-f899-409d-bb8e-6e2b3e6332f4

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 58 through 81, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 24
      (rightCached000.drop 58) (rightRows000.drop 58) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared46
end
