-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.right_parallel_000_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:02:58.314382+00:00
-- url     : https://prove2.me/submissions/ac48ba4b-915c-4bea-842e-95a40937b380

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData28Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared28
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 60 through 71, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 12
      (PairLightPrepared28.rightCached.drop 60) (PairLightPrepared28.rightRows.drop 60) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
