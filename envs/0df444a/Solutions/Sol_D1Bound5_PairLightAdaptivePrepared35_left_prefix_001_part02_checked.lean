-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared35.left_prefix_001_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:04:51.940935+00:00
-- url     : https://prove2.me/submissions/b72a9856-a488-41b0-b946-edc71dfa98db

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData35_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 240 through 368; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared35.sieve 129
      (leftCached001.drop 108) (leftRows001.drop 108) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared35
end
