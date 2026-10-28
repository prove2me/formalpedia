-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared17.left_prefix_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:12.371057+00:00
-- url     : https://prove2.me/submissions/53fe9ba5-067f-4468-99d6-b1f979e3869b

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData17_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData17_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 59 through 93; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared17.sieve 35
      (leftCached000.drop 59) (leftRows000.drop 59) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared17
end
