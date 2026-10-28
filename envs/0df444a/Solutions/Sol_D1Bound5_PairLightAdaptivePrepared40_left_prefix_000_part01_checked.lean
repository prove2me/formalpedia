-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared40.left_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:20:37.559889+00:00
-- url     : https://prove2.me/submissions/16b24c19-d10c-4810-9b8f-91886eb2993f

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData40_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 28 through 58; each retains its entire original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 2 PairLightPrepared40.sieve 31
      (leftCached000.drop 28) (leftRows000.drop 28) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared40
end
