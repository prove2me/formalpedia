-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared17.right_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:31:01.8812+00:00
-- url     : https://prove2.me/submissions/b9699320-1295-40fa-ad65-bcfce72c3844

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 96 through 136; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 41
      (rightCached000.drop 96) (rightRows000.drop 96) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared17
end
