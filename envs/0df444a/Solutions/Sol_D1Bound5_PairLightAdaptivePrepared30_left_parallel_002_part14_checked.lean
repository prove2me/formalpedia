-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared30.left_parallel_002_part14_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:26.808019+00:00
-- url     : https://prove2.me/submissions/7e650efa-ab96-4c8d-ab29-2c10d3ccd81b

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

/-- Original heads 380 through 391, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.leftCached.drop 380) (PairLightPrepared30.leftRows.drop 380) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared30
end
