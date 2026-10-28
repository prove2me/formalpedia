-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared30.right_parallel_001_part10_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:35:43.201219+00:00
-- url     : https://prove2.me/submissions/ed8b3d72-5c98-42ef-9267-1c772b5fd00c

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

/-- Original heads 212 through 213, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 2
      (PairLightPrepared30.rightCached.drop 212) (PairLightPrepared30.rightRows.drop 212) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared30
end
