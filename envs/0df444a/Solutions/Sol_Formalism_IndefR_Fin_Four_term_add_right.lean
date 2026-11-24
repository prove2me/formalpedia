-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.term_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:19:26.670155+00:00
-- url     : https://prove2.me/submissions/d806fadf-569e-43ec-927a-237c22b72880

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Theorems.Thm_Formalism_IndefR_Fin_Four_coef_add_right

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
include hfinX
namespace Formalism.IndefR.Fin.Four
theorem _root_.solution (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y')
    (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1) (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
    (hfY : ∀ u ∈ L ⊓ Y, ρ u f₀ = f₀) (Φ : W → ℂ) (a : W) {y : W} (hy : y ∈ Y) {μ : W} (hμ : μ ∈ L ⊓ Y) :
    term ρ χ L X f₀ Φ a (y + μ) = term ρ χ L X f₀ Φ a y := by
  unfold term
  rw [coef_add_right hfinX hχr hLL Φ a y hμ, hY y hy μ (AddSubgroup.mem_inf.mp hμ).2, Module.End.mul_apply,
    hfY μ hμ]
end Formalism.IndefR.Fin.Four
