-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared38.right_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:30:30.14168+00:00
-- url     : https://prove2.me/submissions/22cbbe45-754a-4c5a-b8a4-6d81ab5cd6cb

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 38 through 81; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 44
      (rightCached000.drop 38) (rightRows000.drop 38) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared38
end
