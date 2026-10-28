-- Prove2me | solution 1 for D1Bound5.PairLightPrepared9.left_signatures_checked
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T05:40:15.263476+00:00
-- url     : https://prove2.me/submissions/c3fc4492-75c7-41f5-9c35-063882e8a624

import Init
import Mathlib.Data.List.Basic
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairLightData9_Definitions_001
import Theorems.Thm_D1Bound5_PairLightAdaptivePrepared9_left_signatures_checked

section
namespace D1Bound5.PairLightPrepared9
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.solution :
    (leftCached.all fun x => decide (x.2 = pairLightCoordinateSignature sieve x.1)) = true :=
  PairLightAdaptivePrepared9.left_signatures_checked





end D1Bound5.PairLightPrepared9
end
