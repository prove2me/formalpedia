-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part22_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:58:50.135232+00:00
-- url     : https://prove2.me/submissions/86f5e0c6-5c36-4f20-a215-9108743fc710

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData23Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 476 through 481, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 6
      (PairLightPrepared23.leftCached.drop 476) (PairLightPrepared23.leftRows.drop 476) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared23
end
