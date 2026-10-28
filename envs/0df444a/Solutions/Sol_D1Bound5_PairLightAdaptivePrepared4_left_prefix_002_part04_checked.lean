-- Prove2me | solution 1 for D1Bound5.PairLightAdaptivePrepared4.left_prefix_002_part04_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:36:13.448241+00:00
-- url     : https://prove2.me/submissions/795b745f-8129-4a40-a4aa-9eb65e1f1161

import Init
import Definitions.Def_D1Bound5_PairLightArithmeticChunks_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftCached_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4LeftRows_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData4Sieve_Definitions

section
namespace D1Bound5.PairLightAdaptivePrepared4
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Original heads 218 through 235, retaining complete original tails. -/
theorem _root_.solution :
    pairLightSelectedFloorPrefixBool 0 1 PairLightPrepared4.sieve 18
      (PairLightPrepared4.leftCached.drop 218)
      (PairLightPrepared4.leftRows.drop 218) = true := by
  decide +kernel

end D1Bound5.PairLightAdaptivePrepared4
end
