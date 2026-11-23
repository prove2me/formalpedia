-- Prove2me | solution 1 for Csg.idsCSG_bwInd_two_healthy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:10.706809+00:00
-- url     : https://prove2.me/submissions/bb794b92-9ace-4d65-b700-f48d0b1f2a25

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_idsCSG_bwInd_two

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : idsCSG.bwInd (fun _ => 0) 2 .healthy = 25 / 21 :=
  idsCSG_bwInd_two .healthy
end Csg
