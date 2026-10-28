-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_003_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:19:40.355523+00:00
-- url     : https://prove2.me/submissions/b71bd2a0-0dce-4252-855e-8d267ff1e20b

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 250 through 250; every full later-vertex tail retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 1
      (leftCached003.drop 72) (leftRows003.drop 72) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
