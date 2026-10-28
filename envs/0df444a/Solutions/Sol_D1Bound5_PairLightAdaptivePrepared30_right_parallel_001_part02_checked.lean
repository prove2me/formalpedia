-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared30.right_parallel_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:43:36.510813+00:00
-- url     : https://prove2.me/submissions/12c5a469-c0d7-4f6b-ad0c-bb7a7d38b1a9

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

/-- Original heads 116 through 127, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 116) (PairLightPrepared30.rightRows.drop 116) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared30
end
