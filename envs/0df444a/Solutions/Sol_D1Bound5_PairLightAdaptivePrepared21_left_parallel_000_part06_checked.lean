-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.left_parallel_000_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:20:27.716993+00:00
-- url     : https://prove2.me/submissions/147951e2-65c0-4eca-9f8f-7a297bfbd641

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

/-- Original heads 72 through 81, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 10
      (PairLightPrepared21.leftCached.drop 72) (PairLightPrepared21.leftRows.drop 72) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared21
end
