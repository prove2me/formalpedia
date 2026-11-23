-- Prove2me | solution 1 for Csg.idsCSG_stageValue_compromised_eq_healthy_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:58:58.652794+00:00
-- url     : https://prove2.me/submissions/82aa81b9-e497-48a8-a025-460003a8b910

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_idsCSG_stageGame_compromised_eq_healthy_add_one
import Theorems.Thm_Csg_MatrixGame_value_add_const


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : IDSState → ℝ) :
    idsCSG.stageValue .compromised v = idsCSG.stageValue .healthy v + 1 :=
  MatrixGame.value_add_const 1 (idsCSG_stageGame_compromised_eq_healthy_add_one v)
end Csg
