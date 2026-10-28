-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared1.right_prefix_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:49:31.990224+00:00
-- url     : https://prove2.me/submissions/55b04032-b4cc-4375-93ce-b0a2e2850f20

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 82 through 107, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 26
      (rightCached000.drop 82) (rightRows000.drop 82) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared1
end
