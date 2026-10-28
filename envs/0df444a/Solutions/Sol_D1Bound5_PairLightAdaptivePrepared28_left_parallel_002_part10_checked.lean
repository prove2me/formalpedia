-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.left_parallel_002_part10_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:27:28.143275+00:00
-- url     : https://prove2.me/submissions/47d8e59a-9cd4-46c2-a708-576d41c26c5b

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 304 through 315, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 304) (PairLightPrepared28.leftRows.drop 304) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
