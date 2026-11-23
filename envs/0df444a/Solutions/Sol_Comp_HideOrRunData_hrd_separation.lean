-- Prove2me | solution 1 for Comp.HideOrRunData.hrd_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:40:15.225497+00:00
-- url     : https://prove2.me/submissions/7dbad09a-6999-4751-b2b9-ee6fbce4e687

import Definitions.Def_Comp_ModelDataQualitative
import Definitions.Def_Comp_HideOrRunDataQ
import Theorems.Thm_Comp_HideOrRunData_hrd_answers_LF
import Theorems.Thm_Comp_HideOrRunData_hrd_answers_AF
import Theorems.Thm_Comp_CsgQ_AF_eq_of_answers
import Theorems.Thm_Comp_CsgQ_LF_eq_of_answers
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
import Theorems.Thm_Comp_ModelData_mem_aOf
import Theorems.Thm_Comp_ModelData_mem_aTr
import Theorems.Thm_Comp_ModelData_mem_apre1Of
import Theorems.Thm_Comp_ModelData_mem_apre1Tr
import Theorems.Thm_Comp_ModelData_mem_bOf
import Theorems.Thm_Comp_ModelData_mem_bTr
import Theorems.Thm_Comp_ModelData_mem_enabled1
import Theorems.Thm_Comp_ModelData_mem_enabled2
import Theorems.Thm_Comp_ModelData_mem_lpre1Of
import Theorems.Thm_Comp_ModelData_mem_lpre1Tr
import Theorems.Thm_Comp_ModelData_mem_pre1Of
import Theorems.Thm_Comp_ModelData_padFin1_mem
import Theorems.Thm_Comp_ModelData_padFin2_mem
import Theorems.Thm_Comp_ModelData_padSat1_empty
import Theorems.Thm_Comp_ModelData_padSat2_empty
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
attribute [local simp] Comp.ModelData.mem_aOf
attribute [local simp] Comp.ModelData.mem_aTr
attribute [local simp] Comp.ModelData.mem_apre1Of
attribute [local simp] Comp.ModelData.mem_apre1Tr
attribute [local simp] Comp.ModelData.mem_bOf
attribute [local simp] Comp.ModelData.mem_bTr
attribute [local simp] Comp.ModelData.mem_enabled1
attribute [local simp] Comp.ModelData.mem_enabled2
attribute [local simp] Comp.ModelData.mem_lpre1Of
attribute [local simp] Comp.ModelData.mem_lpre1Tr
attribute [local simp] Comp.ModelData.mem_pre1Of
attribute [local simp] Comp.ModelData.padFin1_mem
attribute [local simp] Comp.ModelData.padFin2_mem
attribute [local simp] Comp.ModelData.padSat1_empty
attribute [local simp] Comp.ModelData.padSat2_empty
attribute [local simp] Comp.ModelData.toCsgQ_K
attribute [local simp] Comp.fixAux_zero



set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Comp.HideOrRunData
namespace Comp.HideOrRunData
theorem _root_.solution :
    (0 : Fin hrd.nStates) ∈ (hrd.toCsgQ.toCSG hrd_wf).LF ↑hrdTarget ∧
      (0 : Fin hrd.nStates) ∉ (hrd.toCsgQ.toCSG hrd_wf).AF ↑hrdTarget := by
  have hlf := CsgQ.LF_eq_of_answers hrd.toCsgQ hrd_wf hrd_answers_LF
  have haf := CsgQ.AF_eq_of_answers hrd.toCsgQ hrd_wf hrd_answers_AF
  refine ⟨?_, ?_⟩
  · rw [hlf]
    simp only [Fin.isValue, SetLike.mem_coe]
    decide
  · rw [haf]
    simp only [Fin.isValue, SetLike.mem_coe]
    decide
end Comp.HideOrRunData
