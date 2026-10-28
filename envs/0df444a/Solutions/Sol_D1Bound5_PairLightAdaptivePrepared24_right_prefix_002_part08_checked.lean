-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared24.right_prefix_002_part08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:00:19.948581+00:00
-- url     : https://prove2.me/submissions/00b36ae4-befb-4046-abd8-4b2cc06e44ad

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

/-- Original heads 440 through 445, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared24.sieve 6
      (PairLightPrepared24.rightCached.drop 440)
      (PairLightPrepared24.rightRows.drop 440) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared24
end
