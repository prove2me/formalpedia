-- Prove2me | solution 1 for Comp.sum_denseOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:04:16.090408+00:00
-- url     : https://prove2.me/submissions/b938472b-50ba-4f06-9669-30d88b8f14c1

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
import Theorems.Thm_Comp_sum_ite_coe_eq
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
theorem _root_.solution (n : ℕ) (dist : List (ℕ × ℚ)) :
    (∀ p ∈ dist, p.1 < n) →
      ∑ s' : Fin n, denseOf n dist s' = (dist.map Prod.snd).sum := by
  induction dist with
  | nil => intro _; simp [denseOf]
  | cons p rest ih =>
      intro h
      obtain ⟨t, q⟩ := p
      have ht : t < n := h (t, q) (by simp)
      have hrest : ∀ p ∈ rest, p.1 < n := fun p hp => h p (List.mem_cons_of_mem _ hp)
      simp only [denseOf, List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, sum_ite_coe_eq ht q, ih hrest]
end Comp
