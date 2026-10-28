-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared24.left_prefix_002_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:52.324901+00:00
-- url     : https://prove2.me/submissions/66617e86-fbd7-4ba6-8a6f-b4ef2e028501

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

/-- Original heads 296 through 319, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.leftCached.drop 296)
      (PairLightPrepared24.leftRows.drop 296) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared24
end
