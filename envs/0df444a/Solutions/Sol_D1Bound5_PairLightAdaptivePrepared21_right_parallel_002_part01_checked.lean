-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.right_parallel_002_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:47:51.943493+00:00
-- url     : https://prove2.me/submissions/95ae2095-0101-4da3-8f65-d0f0c3904aaf

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData21Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 196 through 207, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.rightCached.drop 196) (PairLightPrepared21.rightRows.drop 196) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared21
end
