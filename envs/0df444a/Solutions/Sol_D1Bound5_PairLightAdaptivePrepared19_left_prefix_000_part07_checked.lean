-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.left_prefix_000_part07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:34:19.307466+00:00
-- url     : https://prove2.me/submissions/3d42b7ab-c738-41b0-9465-27ec902ccc5e

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

/-- Original heads 84 through 95, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 12
      (PairLightPrepared19.leftCached.drop 84)
      (PairLightPrepared19.leftRows.drop 84) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared19
end
