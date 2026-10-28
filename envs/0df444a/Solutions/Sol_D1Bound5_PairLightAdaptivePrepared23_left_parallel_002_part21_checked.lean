-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared23.left_parallel_002_part21_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:06:35.983688+00:00
-- url     : https://prove2.me/submissions/b0c7f7b1-2fbe-40ca-b941-91d830a34dd8

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

/-- Original heads 464 through 475, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared23.sieve 12
      (PairLightPrepared23.leftCached.drop 464) (PairLightPrepared23.leftRows.drop 464) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared23
end
