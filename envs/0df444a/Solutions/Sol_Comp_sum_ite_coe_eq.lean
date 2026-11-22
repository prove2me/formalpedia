-- Prove2me | solution 1 for Comp.sum_ite_coe_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:45:55.75117+00:00
-- url     : https://prove2.me/submissions/7264aa57-9de2-4a10-8df2-a4353904b36f

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
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



set_option autoImplicit true
open Comp
namespace Comp
theorem _root_.solution {n t : ℕ} (ht : t < n) (q : ℚ) :
    ∑ s' : Fin n, (if (s' : ℕ) = t then q else 0) = q := by
  have hcond : ∀ s' : Fin n, ((s' : ℕ) = t) ↔ (s' = (⟨t, ht⟩ : Fin n)) := by
    intro s'
    constructor
    · intro hv
      exact Fin.ext hv
    · intro he
      rw [he]
  calc ∑ s' : Fin n, (if (s' : ℕ) = t then q else 0)
      = ∑ s' : Fin n, (if s' = (⟨t, ht⟩ : Fin n) then q else 0) := by
        refine Finset.sum_congr rfl fun s' _ => ?_
        simp only [hcond s']
    _ = q := by simp
end Comp
