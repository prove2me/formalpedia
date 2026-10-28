-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared28.right_parallel_000_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:51:36.168087+00:00
-- url     : https://prove2.me/submissions/b887adf7-c57d-42bf-9dc9-5a649677639b

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

/-- Original heads 72 through 81, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared28.sieve 10
      (PairLightPrepared28.rightCached.drop 72) (PairLightPrepared28.rightRows.drop 72) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared28
end
