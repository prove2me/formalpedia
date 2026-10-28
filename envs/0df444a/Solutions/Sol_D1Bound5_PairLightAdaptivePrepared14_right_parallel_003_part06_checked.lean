-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared14.right_parallel_003_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:19.215508+00:00
-- url     : https://prove2.me/submissions/d71daa08-c9d9-4f93-ac23-630c9e0d24cd

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

/-- Original heads 489 through 495, with every original tail comparison. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 2 PairLightPrepared14.sieve 7
      (PairLightPrepared14.rightCached.drop 489) (PairLightPrepared14.rightRows.drop 489) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared14
end
