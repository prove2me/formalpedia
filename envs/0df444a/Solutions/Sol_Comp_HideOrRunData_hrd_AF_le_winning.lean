-- Prove2me | solution 1 for Comp.HideOrRunData.hrd_AF_le_winning
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:46:34.262668+00:00
-- url     : https://prove2.me/submissions/b056b225-c073-4b96-b478-88f32bbfbb13

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ
import Theorems.Thm_Comp_HideOrRunData_hrd_nonzero
import Theorems.Thm_Comp_CsgQ_AF_le_univ
import Theorems.Thm_Comp_ModelData_AF_le_of_data_step


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData
namespace Comp.HideOrRunData
theorem _root_.solution : (hrd.toCsgQ.toCSG hrd_wf).AF ↑hrdTarget
    ≤ (↑hrdWinning : Set (Fin hrd.nStates)) :=
  hrd.AF_le_of_data_step hrd_shape hrd_stochastic hrd_nonzero hrdTarget Finset.univ
    hrdWinning 2 (by decide) (by decide) (CsgQ.AF_le_univ hrd.toCsgQ hrd_wf hrdTarget)
end Comp.HideOrRunData
