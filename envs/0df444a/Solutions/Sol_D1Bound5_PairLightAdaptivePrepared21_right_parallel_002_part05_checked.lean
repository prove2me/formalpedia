-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared21.right_parallel_002_part05_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:30:21.493458+00:00
-- url     : https://prove2.me/submissions/c583cd17-614c-44c1-9d4c-d69d4fcbe4f8

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

/-- Original heads 244 through 255, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared21.sieve 12
      (PairLightPrepared21.rightCached.drop 244) (PairLightPrepared21.rightRows.drop 244) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared21
end
