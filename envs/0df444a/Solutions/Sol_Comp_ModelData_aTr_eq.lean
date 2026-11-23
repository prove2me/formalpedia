-- Prove2me | solution 1 for Comp.ModelData.aTr_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:21:12.111655+00:00
-- url     : https://prove2.me/submissions/a462fdd9-09ec-4c78-94c0-04d902eb72e2

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
import Theorems.Thm_Comp_ModelData_supportF_eq
import Theorems.Thm_Comp_ModelData_supportOf_padFin2
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
theorem _root_.solution [NeZero d.nAct1] [NeZero d.nAct2] (hs : d.Shape) (hnn : d.Nonneg)
    (hnz : d.Nonzero) (s : Fin d.nStates) (v2 : Finset (Fin d.nAct2))
    (hv2 : d.PadSat2 hs s v2) (y : Finset (Fin d.nStates)) :
    d.aTr hs v2 y s = d.toCsgQ.aF v2 y s ∩ d.enabled1 hs s := by
  ext a1
  simp only [mem_aTr, Finset.mem_inter, CsgQ.mem_aF, d.supportF_eq hs hnn hnz]
  constructor
  · rintro ⟨hm, h⟩
    refine ⟨fun a2 => ?_, hm⟩
    rcases h (d.padFin2 hs s a2) (d.padFin2_mem hs s a2) with hv | hsub
    · exact Or.inl ((hv2 a2).mpr hv)
    · rw [d.supportOf_padFin2 hs s a1 a2] at hsub
      exact Or.inr hsub
  · rintro ⟨h, hm⟩
    exact ⟨hm, fun a2 _ => h a2⟩
end Comp.ModelData
