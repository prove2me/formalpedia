-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared12.right_prefix_000_part02_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:07:44.430995+00:00
-- url     : https://prove2.me/submissions/9efc4370-c0df-43fc-a475-9a33b9ec947e

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 60 through 94; every head retains its complete original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 35
      (rightCached000.drop 60) (rightRows000.drop 60) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared12
end
