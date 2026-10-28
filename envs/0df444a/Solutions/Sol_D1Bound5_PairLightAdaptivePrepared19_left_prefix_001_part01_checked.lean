-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.left_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:45:20.312431+00:00
-- url     : https://prove2.me/submissions/34d5b08a-763c-4002-8489-d91989ce11c8

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 125 through 148, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.leftCached.drop 125)
      (PairLightPrepared19.leftRows.drop 125) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared19
end
