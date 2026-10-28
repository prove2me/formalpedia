-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared9.left_prefix_000_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:50:59.561982+00:00
-- url     : https://prove2.me/submissions/488fcf51-21d5-4339-9eba-be3260000c12

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData9_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared9
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Heads 0 through 218; every head retains its entire tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared9.sieve 219
      leftCached000 leftRows000 = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared9
end
