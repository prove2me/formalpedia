-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.right_prefix_001_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:30:29.410374+00:00
-- url     : https://prove2.me/submissions/f995514d-9d6e-4444-8395-729722568531

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData7Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared7
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 202 through 225, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.rightCached.drop 202)
      (PairLightPrepared7.rightRows.drop 202) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared7
end
