-- Prove2me | solution 1 for Comp.ModelData.lpre1F_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:23:50.177534+00:00
-- url     : https://prove2.me/submissions/7f5ee221-60ae-4e7c-9bd4-3f5049f67b95

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_mem_pre1Of
import Theorems.Thm_Comp_ModelData_padSat1_empty
import Theorems.Thm_Comp_ModelData_padSat2_empty
import Theorems.Thm_Comp_ModelData_mem_aTr
import Theorems.Thm_Comp_ModelData_mem_bTr
import Theorems.Thm_Comp_ModelData_mem_apre1Tr
import Theorems.Thm_Comp_ModelData_mem_lpre1Tr
import Theorems.Thm_Comp_ModelData_mem_aOf
import Theorems.Thm_Comp_ModelData_mem_bOf
import Theorems.Thm_Comp_ModelData_bF_eq
import Theorems.Thm_Comp_ModelData_mem_apre1Of
import Theorems.Thm_Comp_ModelData_mem_lpre1Of
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
attribute [local simp] Comp.ModelData.mem_bTr
attribute [local simp] Comp.ModelData.mem_apre1Tr
attribute [local simp] Comp.ModelData.mem_lpre1Tr
attribute [local simp] Comp.ModelData.mem_aOf
attribute [local simp] Comp.ModelData.mem_bOf
attribute [local simp] Comp.ModelData.mem_apre1Of
attribute [local simp] Comp.ModelData.mem_lpre1Of

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (w : Fin d.nStates → Finset (Fin d.nAct1)) (x : Finset (Fin d.nStates)) :
    d.toCsgQ.lpre1F w x = d.lpre1Of hs w x := by
  ext s
  simp only [CsgQ.mem_lpre1F, mem_lpre1Of, d.bF_eq hs hnn hnz]
end Comp.ModelData
