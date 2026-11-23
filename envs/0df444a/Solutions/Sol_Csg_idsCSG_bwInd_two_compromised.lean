-- Prove2me | solution 1 for Csg.idsCSG_bwInd_two_compromised
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:13.680241+00:00
-- url     : https://prove2.me/submissions/d8769476-1fdb-41cd-a8ad-27ac7649176e

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_idsCSG_bwInd_two

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : idsCSG.bwInd (fun _ => 0) 2 .compromised = 46 / 21 :=
  idsCSG_bwInd_two .compromised
end Csg
