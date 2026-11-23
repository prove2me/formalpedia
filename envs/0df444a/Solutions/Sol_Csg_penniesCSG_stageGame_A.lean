-- Prove2me | solution 1 for Csg.penniesCSG_stageGame_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:25:57.916495+00:00
-- url     : https://prove2.me/submissions/68e08115-bbf3-423f-b80a-3807c9100cb5

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
import Theorems.Thm_Csg_penniesCSG_expect
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (i j : Fin 2) :
    (penniesCSG.stageGame () (0 : Unit → ℝ)).A i j = penniesMatrix.A i j := by
  change penniesCSG.r () i j + penniesCSG.expect () i j 0 = penniesMatrix.A i j
  rw [penniesCSG_expect]
  simp [penniesCSG]
end Csg
