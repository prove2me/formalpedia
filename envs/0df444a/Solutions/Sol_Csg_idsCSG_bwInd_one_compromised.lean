-- Prove2me | solution 1 for Csg.idsCSG_bwInd_one_compromised
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:06.685516+00:00
-- url     : https://prove2.me/submissions/d189c204-de4a-4e30-ba06-5735cdad2919

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_idsCSG_bwInd_one

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : idsCSG.bwInd (fun _ => 0) 1 .compromised = 4 / 3 :=
  idsCSG_bwInd_one .compromised
end Csg
