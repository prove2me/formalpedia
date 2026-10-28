-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.left_prefix_002_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:19:12.889346+00:00
-- url     : https://prove2.me/submissions/f114bdf3-30e0-4905-925b-9d2c879f7aa6

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 412 through 431, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 20
      (PairLightPrepared7.leftCached.drop 412)
      (PairLightPrepared7.leftRows.drop 412) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared7
end
