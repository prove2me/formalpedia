-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared36.left_parallel_000_part03_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:38:39.648537+00:00
-- url     : https://prove2.me/submissions/8e47e816-851c-42d3-b7aa-7b0ac6f02e1f

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

/-- Original heads 36 through 47, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared36.sieve 12
      (PairLightPrepared36.leftCached.drop 36) (PairLightPrepared36.leftRows.drop 36) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared36
end
