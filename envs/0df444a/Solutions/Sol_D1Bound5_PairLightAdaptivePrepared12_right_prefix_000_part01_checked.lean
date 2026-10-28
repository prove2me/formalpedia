-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared12.right_prefix_000_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:16:36.462429+00:00
-- url     : https://prove2.me/submissions/88996a9d-fb50-4e79-9acd-d3ee3925820b

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData12_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData12_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 29 through 59; every head retains its complete original tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared12.sieve 31
      (rightCached000.drop 29) (rightRows000.drop 29) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared12
end
