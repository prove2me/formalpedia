-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.left_parallel_001_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:10:16.908845+00:00
-- url     : https://prove2.me/submissions/4398dad8-0daa-43ab-9219-8fc3ff3ea91f

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

/-- Original heads 130 through 141, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.leftCached.drop 130) (PairLightPrepared21.leftRows.drop 130) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared21
end
