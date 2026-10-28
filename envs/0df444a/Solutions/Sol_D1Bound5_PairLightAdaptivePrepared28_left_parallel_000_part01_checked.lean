-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.left_parallel_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:32:57.677759+00:00
-- url     : https://prove2.me/submissions/a69f36e7-ce40-401a-b727-0f9b7c73b1e7

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

/-- Original heads 12 through 23, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.leftCached.drop 12) (PairLightPrepared28.leftRows.drop 12) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
