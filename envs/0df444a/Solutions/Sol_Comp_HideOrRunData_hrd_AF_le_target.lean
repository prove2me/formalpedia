-- Prove2me | solution 1 for Comp.HideOrRunData.hrd_AF_le_target
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:39:41.2828+00:00
-- url     : https://prove2.me/submissions/9fe87f42-32b7-4a36-9dac-c5e56d285757

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ
import Theorems.Thm_Comp_HideOrRunData_hrd_nonzero
import Theorems.Thm_Comp_HideOrRunData_hrd_AF_le_winning
import Theorems.Thm_Comp_ModelData_AF_le_of_data_step


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData
namespace Comp.HideOrRunData
theorem _root_.solution : (hrd.toCsgQ.toCSG hrd_wf).AF ↑hrdTarget
    ≤ (↑hrdTarget : Set (Fin hrd.nStates)) :=
  hrd.AF_le_of_data_step hrd_shape hrd_stochastic hrd_nonzero hrdTarget hrdWinning
    hrdTarget 1 (by decide) (by decide) hrd_AF_le_winning
end Comp.HideOrRunData
