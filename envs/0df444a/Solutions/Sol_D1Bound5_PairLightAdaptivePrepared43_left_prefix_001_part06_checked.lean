-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.left_prefix_001_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:32:42.579781+00:00
-- url     : https://prove2.me/submissions/2bde177b-0bd2-4686-a22d-c9b534c22579

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData43Left_Definitions_003

section
namespace D1Bound5.PairLightAdaptivePrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 163 through 174, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 12
      (PairLightPrepared43.leftCached.drop 163)
      (PairLightPrepared43.leftRows.drop 163) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared43
end
