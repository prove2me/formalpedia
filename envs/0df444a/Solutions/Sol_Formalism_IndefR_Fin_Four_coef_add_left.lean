-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.coef_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:14:01.447951+00:00
-- url     : https://prove2.me/submissions/e1885236-f81d-4f99-87fc-f50f0006924f

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Theorems.Thm_Formalism_IndefR_Fin_Four_integ_eq
import Theorems.Thm_Formalism_IndefR_Fin_Four_integ_shift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.Fin Formalism.IndefR.Fin.Four
variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]
variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W} {f₀ : V}
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y) (hχ0 : ∀ t y, χ t y ≠ 0)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X)))
include hχl hχ0 hfinX
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution (Φ : W → ℂ) (a y : W) {l : W} (hl : l ∈ L ⊓ X) :
    coef χ L X Φ (a + l) y = χ l y * coef χ L X Φ a y := by
  have hc := hχ0 l y
  have hH : ∀ t, Φ (a + l + t) * (χ t y)⁻¹ = χ l y * (Φ (a + (t + l)) * (χ (t + l) y)⁻¹) := by
    intro t
    have e : (χ t y)⁻¹ = χ l y * (χ (t + l) y)⁻¹ := by
      rw [hχl, mul_inv, mul_left_comm, mul_inv_cancel₀ hc, mul_one]
    rw [e, add_comm t l, ← add_assoc]
    ring
  have hiff : ∀ k, IsInv k (L ⊓ X) (fun t => Φ (a + l + t) * (χ t y)⁻¹) ↔
      IsInv k (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹) := by
    intro k
    unfold IsInv
    simp only [hH]
    constructor
    · intro h t ht u hu
      have := h (t - l) (sub_mem ht hl) u hu
      rw [sub_add_cancel, show t - l + k • u + l = t + k • u by abel] at this
      exact mul_left_cancel₀ hc this
    · intro h t ht u hu
      rw [show t + k • u + l = (t + l) + k • u by abel, h (t + l) (add_mem ht hl) u hu]
  unfold coef
  by_cases h0 : ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => Φ (a + t) * (χ t y)⁻¹)
  · obtain ⟨k, hk, hinv⟩ := h0
    have hinv1 := (hiff k).mpr hinv
    have hinvs : IsInv k (L ⊓ X) (fun t => Φ (a + (t + l)) * (χ (t + l) y)⁻¹) := by
      intro t ht u hu
      beta_reduce
      rw [show t + k • u + l = (t + l) + k • u by abel]
      exact hinv (t + l) (add_mem ht hl) u hu
    rw [integ_eq hfinX hk hinv1, ← integ_shift hfinX hk hinv hl, integ_eq hfinX hk hinvs]
    unfold avg
    haveI := hfinX k hk
    simp only [hH]
    rw [← mul_finsum]
    ring
  · have h1 : ¬ ∃ k, 0 < k ∧ IsInv k (L ⊓ X) (fun t => Φ (a + l + t) * (χ t y)⁻¹) :=
      fun ⟨k, hk, hi⟩ => h0 ⟨k, hk, (hiff k).mp hi⟩
    unfold integ
    rw [dif_neg h1, dif_neg h0, mul_zero]
end Formalism.IndefR.Fin.Four
