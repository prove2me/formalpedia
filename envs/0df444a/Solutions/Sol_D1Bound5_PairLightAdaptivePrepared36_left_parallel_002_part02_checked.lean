-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.left_parallel_002_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:54:57.217448+00:00
-- url     : https://prove2.me/submissions/afd919ce-6a3e-469e-8ddd-9dbd066014c0

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData36Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared36
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 191 through 202, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 191) (PairLightPrepared36.leftRows.drop 191) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared36
end
