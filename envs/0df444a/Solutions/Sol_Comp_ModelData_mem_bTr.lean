-- Prove2me | solution 1 for Comp.ModelData.mem_bTr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:55:34.543134+00:00
-- url     : https://prove2.me/submissions/53456fd8-51ea-4fd7-93c9-71ece71cf233

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_mem_pre1Of
import Theorems.Thm_Comp_ModelData_padSat1_empty
import Theorems.Thm_Comp_ModelData_padSat2_empty
import Theorems.Thm_Comp_ModelData_mem_aTr
import Theorems.Thm_Comp_CsgQ_castIcc_coe
import Theorems.Thm_Comp_CsgQ_coe_supportF
import Theorems.Thm_Comp_CsgQ_mem_aF
import Theorems.Thm_Comp_CsgQ_mem_apre1F
import Theorems.Thm_Comp_CsgQ_mem_bF
import Theorems.Thm_Comp_CsgQ_mem_gStepF
import Theorems.Thm_Comp_CsgQ_mem_lpre1F
import Theorems.Thm_Comp_CsgQ_mem_pre1F
import Theorems.Thm_Comp_CsgQ_mem_supportF
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
import Theorems.Thm_Comp_ModelData_mem_enabled1
import Theorems.Thm_Comp_ModelData_mem_enabled2
import Theorems.Thm_Comp_ModelData_padFin1_mem
import Theorems.Thm_Comp_ModelData_padFin2_mem
import Theorems.Thm_Comp_ModelData_toCsgQ_K
import Theorems.Thm_Comp_fixAux_zero
attribute [local simp] Comp.CsgQ.castIcc_coe
attribute [local simp] Comp.CsgQ.coe_supportF
attribute [local simp] Comp.CsgQ.mem_aF
attribute [local simp] Comp.CsgQ.mem_apre1F
attribute [local simp] Comp.CsgQ.mem_bF
attribute [local simp] Comp.CsgQ.mem_gStepF
attribute [local simp] Comp.CsgQ.mem_lpre1F
attribute [local simp] Comp.CsgQ.mem_pre1F
attribute [local simp] Comp.CsgQ.mem_supportF
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A
attribute [local simp] Comp.ModelData.mem_enabled1
attribute [local simp] Comp.ModelData.mem_enabled2
attribute [local simp] Comp.ModelData.padFin1_mem
attribute [local simp] Comp.ModelData.padFin2_mem
attribute [local simp] Comp.ModelData.toCsgQ_K
attribute [local simp] Comp.fixAux_zero


attribute [local simp] Comp.ModelData.mem_pre1Of
attribute [local simp] Comp.ModelData.padSat1_empty
attribute [local simp] Comp.ModelData.padSat2_empty
attribute [local simp] Comp.ModelData.mem_aTr

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution (hs : d.Shape) (v1 : Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates))
    (s : Fin d.nStates) (a2 : Fin d.nAct2) :
    a2 ∈ d.bTr hs v1 x s ↔
      a2 ∈ d.enabled2 hs s ∧ ∃ a1 ∈ v1, (d.supportOf hs s a1 a2 ∩ x).Nonempty := by
  simp only [bTr, Finset.mem_filter]
end Comp.ModelData
