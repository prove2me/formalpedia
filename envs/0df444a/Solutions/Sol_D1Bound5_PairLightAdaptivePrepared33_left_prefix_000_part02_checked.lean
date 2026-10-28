-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared33.left_prefix_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:19:53.788546+00:00
-- url     : https://prove2.me/submissions/9defe7a8-d75c-4f04-92db-cfa94d99adac

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData33_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData33_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared33
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 59 through 93; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared33.sieve 35
      (leftCached000.drop 59) (leftRows000.drop 59) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared33
end
