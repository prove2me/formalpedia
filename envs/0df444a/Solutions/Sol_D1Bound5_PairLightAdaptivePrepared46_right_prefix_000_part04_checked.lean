-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared46.right_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:29:20.812518+00:00
-- url     : https://prove2.me/submissions/86b4791a-3839-48fa-85aa-08a39c3640c7

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData46_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 82 through 107, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 6 PairLightPrepared46.sieve 26
      (rightCached000.drop 82) (rightRows000.drop 82) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared46
end
