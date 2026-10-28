-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared19.left_prefix_002_part08_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:52:52.696107+00:00
-- url     : https://prove2.me/submissions/bbf96eb9-7b36-44f4-9512-a6673d3356e9

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData19Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 440 through 445, each checked against its complete tail. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 1 1 PairLightPrepared19.sieve 6
      (PairLightPrepared19.leftCached.drop 440)
      (PairLightPrepared19.leftRows.drop 440) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared19
end
