-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared11.right_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:07:58.660303+00:00
-- url     : https://prove2.me/submissions/8ef73447-7da9-4d66-8a85-fdd04deb3374

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData11_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData11Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 16 through 35, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared11.sieve 20
      (rightCached000.drop 16) (rightRows000.drop 16) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared11
end
