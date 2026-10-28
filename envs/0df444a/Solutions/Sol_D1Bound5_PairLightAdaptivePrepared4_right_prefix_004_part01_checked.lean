-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.right_prefix_004_part01_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:15:51.646579+00:00
-- url     : https://prove2.me/submissions/a9d07466-2ed8-4a84-b08d-1a18f369ea56

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

/-- Original heads 441 through 485, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 45
      (PairLightPrepared4.rightCached.drop 441)
      (PairLightPrepared4.rightRows.drop 441) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
