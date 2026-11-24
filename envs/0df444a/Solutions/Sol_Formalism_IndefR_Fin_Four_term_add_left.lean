-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.term_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:19:25.599824+00:00
-- url     : https://prove2.me/submissions/5a420a7a-33b7-4b60-843f-10e4c6f8de2d

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Theorems.Thm_Formalism_IndefR_Fin_Four_chi_neg_left
import Theorems.Thm_Formalism_IndefR_Fin_Four_coef_add_left
import Theorems.Thm_Formalism_IndefR_Fin_Four_coef_eq_zero

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
theorem _root_.solution (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x)) (hfX : ∀ u ∈ L ⊓ X, ρ u f₀ = f₀)
    (Φ : W → ℂ) (hΦ : ∀ t, Φ t ≠ 0 → t ∈ X) (a : W) {y : W} (hy : y ∈ Y) {l : W} (hl : l ∈ L ⊓ X) :
    term ρ χ L X f₀ Φ (a + l) y = term ρ χ L X f₀ Φ a y := by
  by_cases ha : a ∈ X
  · have hl' := AddSubgroup.mem_inf.mp hl
    have hnl : -l ∈ L ⊓ X := neg_mem hl
    have key : ρ (-l) (ρ y f₀) = (χ l y)⁻¹ • ρ y f₀ := by
      have h1 := congrArg (fun T => T f₀) (hXY (-l) (neg_mem hl'.2) y hy)
      simp only [Module.End.mul_apply, LinearMap.smul_apply] at h1
      rw [h1, hfX (-l) hnl, chi_neg_left hχl hχ0]
    unfold term
    rw [coef_add_left hχl hχ0 hfinX Φ a y hl, neg_add, hX (-a) (neg_mem ha) (-l) (neg_mem hl'.2),
      Module.End.mul_apply, key, map_smul, smul_smul, mul_comm (χ l y), mul_assoc, mul_inv_cancel₀ (hχ0 l y), mul_one]
  · have hal : a + l ∉ X := fun h => ha (by simpa using X.sub_mem h (AddSubgroup.mem_inf.mp hl).2)
    unfold term
    rw [coef_eq_zero hfinX Φ hΦ ha, coef_eq_zero hfinX Φ hΦ hal, zero_smul, zero_smul]
end Formalism.IndefR.Fin.Four
