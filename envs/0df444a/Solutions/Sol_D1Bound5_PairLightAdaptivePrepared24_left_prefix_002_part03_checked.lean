-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared24.left_prefix_002_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:23:49.216018+00:00
-- url     : https://prove2.me/submissions/d655f93a-0069-4d8e-a3d5-7ff49c2d344a

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 320 through 343, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.leftCached.drop 320)
      (PairLightPrepared24.leftRows.drop 320) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared24
end
