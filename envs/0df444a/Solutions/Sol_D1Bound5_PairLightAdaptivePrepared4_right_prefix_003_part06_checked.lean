-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.right_prefix_003_part06_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:25:41.806987+00:00
-- url     : https://prove2.me/submissions/2be1c515-76fa-473c-9179-e1d66f1069bd

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4RightRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 402 through 404, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 3
      (PairLightPrepared4.rightCached.drop 402)
      (PairLightPrepared4.rightRows.drop 402) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
