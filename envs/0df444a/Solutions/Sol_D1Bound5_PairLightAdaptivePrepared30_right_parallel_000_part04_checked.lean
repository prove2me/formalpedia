-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared30.right_parallel_000_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:14:21.279577+00:00
-- url     : https://prove2.me/submissions/53a46de0-4025-43b4-90a8-647f2c703fe1

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData30Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 48 through 59, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 48) (PairLightPrepared30.rightRows.drop 48) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared30
end
