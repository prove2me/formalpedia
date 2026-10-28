-- Prove2me | solution 1 for D1Bound5.PairLightPrepared42.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T02:16:24.507257+00:00
-- url     : https://prove2.me/submissions/1110c359-9ed3-4db6-90a4-659b5ca62e19

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_001
import Definitions.Def_D1Bound5_SmallPairLightData42_Definitions_002
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared42_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared42
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared42.left_signatures_checked





end D1Bound5.PairLightPrepared42
end
