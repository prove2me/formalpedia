-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared30.right_parallel_002_part09_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:22:28.192843+00:00
-- url     : https://prove2.me/submissions/b45f1632-5253-420e-9bf8-7c13d9013fc0

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

/-- Original heads 322 through 333, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared30.sieve 12
      (PairLightPrepared30.rightCached.drop 322) (PairLightPrepared30.rightRows.drop 322) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared30
end
