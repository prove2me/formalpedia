-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.left_prefix_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:09:48.858808+00:00
-- url     : https://prove2.me/submissions/f5f10c73-7d22-4bfa-8b6a-d16cdb915e5b

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

/-- Original heads 36 through 47, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 12
      (PairLightPrepared19.leftCached.drop 36)
      (PairLightPrepared19.leftRows.drop 36) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared19
end
