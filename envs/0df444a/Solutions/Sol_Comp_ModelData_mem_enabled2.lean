-- Prove2me | solution 1 for Comp.ModelData.mem_enabled2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:39:56.686406+00:00
-- url     : https://prove2.me/submissions/337335ec-539c-49df-a655-78307d8f4f29

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
import Theorems.Thm_Comp_ModelData_mem_enabled1
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

set_option autoImplicit true
open Comp
namespace Comp
namespace ModelData
theorem _root_.solution (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (a2 : Fin d.nAct2) : a2 ∈ d.enabled2 hs s ↔ (a2 : ℕ) ∈ d.keys2 s := by
  simp only [ModelData.enabled2, Finset.mem_attachFin]
end ModelData
end Comp
