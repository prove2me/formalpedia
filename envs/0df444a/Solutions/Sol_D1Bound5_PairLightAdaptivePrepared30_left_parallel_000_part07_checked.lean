-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared30.left_parallel_000_part07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:37:36.792317+00:00
-- url     : https://prove2.me/submissions/11362af9-e836-4a60-b3e1-c78978a34073

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 84 through 90, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 7
      (PairLightPrepared30.leftCached.drop 84) (PairLightPrepared30.leftRows.drop 84) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared30
end
