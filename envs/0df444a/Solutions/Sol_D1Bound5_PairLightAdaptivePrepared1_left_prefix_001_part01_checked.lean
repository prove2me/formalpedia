-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared1.left_prefix_001_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:10:01.427301+00:00
-- url     : https://prove2.me/submissions/4d3e7147-e72e-4c18-b963-fde973a4cfae

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightAdaptiveData1_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData1Left_Definitions_001

section
namespace D1Bound5.PairLightAdaptivePrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 171 through 212, each compared with its entire remaining tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared1.sieve 42
      (leftCached001.drop 34) (leftRows001.drop 34) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared1
end
