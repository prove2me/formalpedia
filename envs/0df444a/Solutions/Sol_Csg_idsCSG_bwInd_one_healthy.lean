-- Prove2me | solution 1 for Csg.idsCSG_bwInd_one_healthy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:02.691531+00:00
-- url     : https://prove2.me/submissions/9296f5d3-cc80-47a4-9299-660d89d3da0d

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_idsCSG_bwInd_one

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : idsCSG.bwInd (fun _ => 0) 1 .healthy = 1 / 3 :=
  idsCSG_bwInd_one .healthy
end Csg
