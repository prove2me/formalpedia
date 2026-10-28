-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared38.left_prefix_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:22:29.858861+00:00
-- url     : https://prove2.me/submissions/6ff4b661-3bdd-4d2c-8763-a1ae07adf11f

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 82 through 139; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 58
      (leftCached000.drop 82) (leftRows000.drop 82) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared38
end
