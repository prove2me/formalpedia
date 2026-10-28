-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared3.left_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:31:09.379672+00:00
-- url     : https://prove2.me/submissions/58b3e40d-97af-4804-aedc-745af85d2a97

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData3Left_Definitions_002

section
namespace D1Bound5.PairLightAdaptivePrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 36 through 47, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared3.sieve 12
      (PairLightPrepared3.leftCached.drop 36)
      (PairLightPrepared3.leftRows.drop 36) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared3
end
