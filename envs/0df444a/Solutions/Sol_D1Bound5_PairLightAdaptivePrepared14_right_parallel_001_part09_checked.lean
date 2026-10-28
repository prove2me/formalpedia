-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.right_parallel_001_part09_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:44:30.284143+00:00
-- url     : https://prove2.me/submissions/4377ba4e-5c0b-4164-acff-f8cfc05ab361

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData14Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 196 through 201, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 6
      (PairLightPrepared14.rightCached.drop 196) (PairLightPrepared14.rightRows.drop 196) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared14
end
