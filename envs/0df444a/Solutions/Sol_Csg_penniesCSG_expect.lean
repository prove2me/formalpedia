-- Prove2me | solution 1 for Csg.penniesCSG_expect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:24:57.788962+00:00
-- url     : https://prove2.me/submissions/1ddb2614-6e23-4983-8b2c-9f331e45e546

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (i j : Fin 2) (v : Unit → ℝ) :
    penniesCSG.expect () i j v = v () := by
  change ∑ s' : Unit, (penniesCSG.K () i j s').toReal * v s' = v ()
  simp [penniesCSG, PMF.pure_apply]
end Csg
