-- Prove2me | solution 1 for Comp.ModelData.bTr_inter_enabled1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:20:50.382054+00:00
-- url     : https://prove2.me/submissions/8ac55d3f-676c-49a4-b383-e2ae8133ca39

import Definitions.Def_Comp_ModelData
import Definitions.Def_Comp_FixLoop
import Definitions.Def_Comp_ModelDataQualitative
import Theorems.Thm_Comp_ModelData_mem_pre1Of
import Theorems.Thm_Comp_ModelData_padSat1_empty
import Theorems.Thm_Comp_ModelData_padSat2_empty
import Theorems.Thm_Comp_ModelData_mem_aTr
import Theorems.Thm_Comp_ModelData_mem_bTr
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
import Theorems.Thm_Comp_ModelData_supportOf_padFin1
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

set_option autoImplicit true
open Comp
open Comp.ModelData
variable (d : ModelData)
namespace Comp.ModelData
theorem _root_.solution (hs : d.Shape) (s : Fin d.nStates) (v1 : Finset (Fin d.nAct1))
    (hv1 : d.PadSat1 hs s v1) (x : Finset (Fin d.nStates)) :
    d.bTr hs (v1 ∩ d.enabled1 hs s) x s = d.bTr hs v1 x s := by
  ext a2
  simp only [mem_bTr, Finset.mem_inter]
  constructor
  · rintro ⟨hm, a1, ⟨h1, -⟩, hne⟩
    exact ⟨hm, a1, h1, hne⟩
  · rintro ⟨hm, a1, h1, hne⟩
    refine ⟨hm, d.padFin1 hs s a1, ⟨(hv1 a1).mp h1, d.padFin1_mem hs s a1⟩, ?_⟩
    rwa [d.supportOf_padFin1 hs s a1 a2]
end Comp.ModelData
