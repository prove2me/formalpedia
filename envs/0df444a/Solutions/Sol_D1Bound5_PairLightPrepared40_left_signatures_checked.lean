-- Prove2me | solution 1 for D1Bound5.PairLightPrepared40.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T03:21:05.451018+00:00
-- url     : https://prove2.me/submissions/b9c4b412-ce99-4f5b-8455-25727f184540

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared40_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared40.left_signatures_checked





end D1Bound5.PairLightPrepared40
end
