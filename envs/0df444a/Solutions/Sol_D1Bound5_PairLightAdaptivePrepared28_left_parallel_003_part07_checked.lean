-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.left_parallel_003_part07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:19:55.472294+00:00
-- url     : https://prove2.me/submissions/c51f036d-8766-4e2c-ade4-747ac1facf37

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

/-- Original heads 419 through 430, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 419) (PairLightPrepared28.leftRows.drop 419) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
