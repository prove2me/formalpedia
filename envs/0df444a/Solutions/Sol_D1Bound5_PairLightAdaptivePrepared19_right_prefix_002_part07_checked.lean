-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.right_prefix_002_part07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:33:51.643668+00:00
-- url     : https://prove2.me/submissions/f0f5e319-ace8-42e8-884d-c597e74bd778

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 416 through 439, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 24
      (PairLightPrepared19.rightCached.drop 416)
      (PairLightPrepared19.rightRows.drop 416) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared19
end
