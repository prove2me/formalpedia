-- Prove2me | solution 1 for Comp.ModelData.padFin1_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:10:05.032797+00:00
-- url     : https://prove2.me/submissions/1452e832-3113-4ced-9864-06b7eec850b9

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
import Theorems.Thm_Comp_ModelData_pad1_eq_self
import Theorems.Thm_Comp_ModelData_mem_enabled1
import Theorems.Thm_Comp_ModelData_mem_enabled2
import Theorems.Thm_Comp_ModelData_padFin1_mem
import Theorems.Thm_Comp_ModelData_padFin2_mem
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

set_option autoImplicit true
open Comp
namespace Comp
namespace ModelData
theorem _root_.solution (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    {a1 : Fin d.nAct1} (h : a1 ∈ d.enabled1 hs s) : d.padFin1 hs s a1 = a1 := by
  rw [ModelData.mem_enabled1] at h
  exact Fin.ext (d.pad1_eq_self h)
end ModelData
end Comp
