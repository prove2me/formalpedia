-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared7.right_prefix_002_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:42:28.731464+00:00
-- url     : https://prove2.me/submissions/4699a4eb-0236-43e4-a879-33ab708f62dc

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

/-- Original heads 296 through 319, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared7.sieve 24
      (PairLightPrepared7.rightCached.drop 296)
      (PairLightPrepared7.rightRows.drop 296) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared7
end
