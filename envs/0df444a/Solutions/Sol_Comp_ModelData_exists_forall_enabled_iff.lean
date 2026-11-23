-- Prove2me | solution 1 for Comp.ModelData.exists_forall_enabled_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:27:43.537231+00:00
-- url     : https://prove2.me/submissions/2ac49c4c-7423-4903-a2e3-1561d84a1406

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
import Theorems.Thm_Comp_ModelData_padFin1_mem
import Theorems.Thm_Comp_ModelData_padFin2_mem
import Theorems.Thm_Comp_ModelData_padFin1_eq_self
import Theorems.Thm_Comp_ModelData_padFin2_eq_self
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


attribute [local simp] Comp.ModelData.padFin1_mem
attribute [local simp] Comp.ModelData.padFin2_mem

set_option autoImplicit true
open Comp
namespace Comp
namespace ModelData
theorem _root_.solution (d : ModelData) (hs : d.Shape) (s : Fin d.nStates)
    (P : Fin d.nAct1 → Fin d.nAct2 → Prop)
    (hP : ∀ a1 a2, P (d.padFin1 hs s a1) (d.padFin2 hs s a2) ↔ P a1 a2) :
    (∃ a1, ∀ a2, P a1 a2) ↔ (∃ a1 ∈ d.enabled1 hs s, ∀ a2 ∈ d.enabled2 hs s, P a1 a2) := by
  constructor
  · rintro ⟨a1, ha1⟩
    refine ⟨d.padFin1 hs s a1, d.padFin1_mem hs s a1, fun a2 ha2 => ?_⟩
    have h2 := d.padFin2_eq_self hs s ha2
    have hgot := (hP a1 a2).mpr (ha1 a2)
    rwa [h2] at hgot
  · rintro ⟨a1, hm1, ha1⟩
    refine ⟨a1, fun a2 => ?_⟩
    have hgot := ha1 (d.padFin2 hs s a2) (d.padFin2_mem hs s a2)
    have hiff := hP a1 a2
    rw [d.padFin1_eq_self hs s hm1] at hiff
    exact hiff.mp hgot
end ModelData
end Comp
