-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared43.left_prefix_002_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:57:18.338012+00:00
-- url     : https://prove2.me/submissions/a20ce74c-96d8-4395-bc22-4539d5cd6fff

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

/-- Original heads 356 through 379, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 3 PairLightPrepared43.sieve 24
      (PairLightPrepared43.leftCached.drop 356)
      (PairLightPrepared43.leftRows.drop 356) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared43
end
