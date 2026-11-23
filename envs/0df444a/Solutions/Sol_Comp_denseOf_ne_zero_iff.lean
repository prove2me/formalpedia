-- Prove2me | solution 1 for Comp.denseOf_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:07:57.507793+00:00
-- url     : https://prove2.me/submissions/7d586684-59b0-4e6b-b479-f26622c7d395

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_ModelData
import Theorems.Thm_Comp_denseOf_nonneg
import Theorems.Thm_Comp_add_ne_zero_iff_of_nonneg
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
    (∀ p ∈ dist, 0 ≤ p.2) → (∀ p ∈ dist, p.2 ≠ 0) →
      (denseOf n dist s' ≠ 0 ↔ ∃ p ∈ dist, p.1 = (s' : ℕ)) := by
  induction dist with
  | nil => intro _ _; simp [denseOf]
  | cons p rest ih =>
      intro h hz
      obtain ⟨t, q⟩ := p
      have hq : (0 : ℚ) ≤ q := h (t, q) (by simp)
      have hqz : q ≠ 0 := hz (t, q) (by simp)
      have hrest : ∀ p ∈ rest, 0 ≤ p.2 := fun p hp => h p (List.mem_cons_of_mem _ hp)
      have hrestz : ∀ p ∈ rest, p.2 ≠ 0 := fun p hp => hz p (List.mem_cons_of_mem _ hp)
      have hB : (0 : ℚ) ≤ denseOf n rest s' := denseOf_nonneg n rest s' hrest
      have hA : (0 : ℚ) ≤ (if (s' : ℕ) = t then q else 0) := by
        split_ifs
        · exact hq
        · exact le_refl 0
      simp only [denseOf, List.mem_cons]
      rw [add_ne_zero_iff_of_nonneg hA hB, ih hrest hrestz]
      constructor
      · rintro (hne | ⟨p, hp, h1⟩)
        · refine ⟨(t, q), Or.inl rfl, ?_⟩
          split_ifs at hne with hc
          · exact hc.symm
          · exact absurd rfl hne
        · exact ⟨p, Or.inr hp, h1⟩
      · rintro ⟨p, hp, h1⟩
        rcases hp with rfl | hp
        · refine Or.inl ?_
          split_ifs with hc
          · exact hqz
          · exact absurd h1.symm hc
        · exact Or.inr ⟨p, hp, h1⟩
end Comp
