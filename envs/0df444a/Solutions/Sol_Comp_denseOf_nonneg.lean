-- Prove2me | solution 1 for Comp.denseOf_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:46:26.169074+00:00
-- url     : https://prove2.me/submissions/d815fb5a-4980-43d3-a9b2-8494ffaa5205

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
theorem _root_.solution (n : ℕ) (dist : List (ℕ × ℚ)) (s' : Fin n) :
    (∀ p ∈ dist, 0 ≤ p.2) → 0 ≤ denseOf n dist s' := by
  induction dist with
  | nil => intro _; simp [denseOf]
  | cons p rest ih =>
      intro h
      obtain ⟨t, q⟩ := p
      have hq : (0 : ℚ) ≤ q := h (t, q) (by simp)
      have hrest : 0 ≤ denseOf n rest s' := ih fun p hp => h p (List.mem_cons_of_mem _ hp)
      simp only [denseOf]
      split_ifs <;> linarith
end Comp
