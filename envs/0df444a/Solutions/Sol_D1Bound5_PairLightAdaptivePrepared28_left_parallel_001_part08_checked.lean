-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.left_parallel_001_part08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:34:10.078111+00:00
-- url     : https://prove2.me/submissions/f45b3283-2a1d-40f6-9547-9931e991ef46

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

/-- Original heads 178 through 183, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 6
      (PairLightPrepared28.leftCached.drop 178) (PairLightPrepared28.leftRows.drop 178) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
