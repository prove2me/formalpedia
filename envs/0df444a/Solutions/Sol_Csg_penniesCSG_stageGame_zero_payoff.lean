-- Prove2me | solution 1 for Csg.penniesCSG_stageGame_zero_payoff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:27:18.626993+00:00
-- url     : https://prove2.me/submissions/2329375d-a006-451d-b87f-9bac6394db42

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
import Theorems.Thm_Csg_penniesCSG_stageGame_A
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (x y : Fin 2 → ℝ) :
    (penniesCSG.stageGame () (0 : Unit → ℝ)).payoff x y = penniesMatrix.payoff x y := by
  unfold MatrixGame.payoff
  simp only [penniesCSG_stageGame_A]
end Csg
