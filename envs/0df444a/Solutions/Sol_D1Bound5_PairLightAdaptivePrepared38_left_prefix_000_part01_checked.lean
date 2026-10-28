-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared38.left_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:24:07.450245+00:00
-- url     : https://prove2.me/submissions/bc473a3c-4a45-4b99-8526-f88c2239c35f

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData38_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData38_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared38
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 37 through 81; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared38.sieve 45
      (leftCached000.drop 37) (leftRows000.drop 37) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared38
end
