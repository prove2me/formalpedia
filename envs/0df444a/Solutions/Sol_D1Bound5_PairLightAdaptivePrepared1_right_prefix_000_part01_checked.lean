-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared1.right_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:40:51.089962+00:00
-- url     : https://prove2.me/submissions/b553d369-4cfe-49e1-b70c-77a7c886c4fb

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 16 through 35, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 20
      (rightCached000.drop 16) (rightRows000.drop 16) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared1
end
