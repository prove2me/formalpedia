-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared26.left_prefix_000_part10_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:27:31.351946+00:00
-- url     : https://prove2.me/submissions/0eab3bb3-659e-4e86-9f9b-c1105ec4b97e

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData26_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData26_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 30 through 32 of the original first block; every full tail is retained. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared26.sieve 3
      (leftCached000.drop 30) (leftRows000.drop 30) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared26
end
