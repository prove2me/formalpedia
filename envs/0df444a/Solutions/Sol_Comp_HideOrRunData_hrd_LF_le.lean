-- Prove2me | solution 1 for Comp.HideOrRunData.hrd_LF_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:46:27.824676+00:00
-- url     : https://prove2.me/submissions/ebe1b245-126e-47bf-a73a-a958aa2f366b

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ
import Theorems.Thm_Comp_HideOrRunData_hrd_nonzero
import Theorems.Thm_Comp_HideOrRunData_hrd_lw
import Theorems.Thm_Comp_CsgQ_LF_le_univ
import Theorems.Thm_Comp_ModelData_LF_le_of_data_step


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData
set_option maxRecDepth 4000
namespace Comp.HideOrRunData
theorem _root_.solution : (hrd.toCsgQ.toCSG hrd_wf).LF ↑hrdTarget
    ≤ (↑hrdWinning : Set (Fin hrd.nStates)) :=
  hrd.LF_le_of_data_step hrd_shape hrd_stochastic hrd_nonzero 2 hrdTarget Finset.univ
    hrdWinning 2 (fun x s => hrd_lw x Finset.univ s) (by decide) (by decide)
    (CsgQ.LF_le_univ hrd.toCsgQ hrd_wf hrdTarget)
end Comp.HideOrRunData
