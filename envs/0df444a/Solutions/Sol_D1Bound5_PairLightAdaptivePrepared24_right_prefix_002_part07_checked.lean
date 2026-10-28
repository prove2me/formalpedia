-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared24.right_prefix_002_part07_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:08:17.12513+00:00
-- url     : https://prove2.me/submissions/6701db46-ba68-4715-932e-8caccce8c9f9

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData24Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared24
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 416 through 439, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 24
      (PairLightPrepared24.rightCached.drop 416)
      (PairLightPrepared24.rightRows.drop 416) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared24
end
