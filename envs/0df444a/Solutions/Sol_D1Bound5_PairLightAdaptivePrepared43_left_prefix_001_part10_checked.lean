-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.left_prefix_001_part10_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:52:54.556799+00:00
-- url     : https://prove2.me/submissions/1087c203-a1c7-44d7-a0dd-1455f5693ab9

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

/-- Original heads 211 through 211, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 1
      (PairLightPrepared43.leftCached.drop 211)
      (PairLightPrepared43.leftRows.drop 211) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared43
end
