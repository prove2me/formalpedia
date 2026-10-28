-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared48.left_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:36.602995+00:00
-- url     : https://prove2.me/submissions/3b5b4b40-f6d4-4498-b15f-506dd7f1b99c

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData48_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 28 through 58; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 8 PairLightPrepared48.sieve 31
      (leftCached000.drop 28) (leftRows000.drop 28) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared48
end
