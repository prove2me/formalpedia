-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.left_parallel_002_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:23:13.082723+00:00
-- url     : https://prove2.me/submissions/4bd013f7-77fc-4b16-a393-98f65c1eec5f

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 256 through 267, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 256) (PairLightPrepared21.leftRows.drop 256) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared21
end
