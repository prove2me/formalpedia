-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.coef_add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:13:30.874395+00:00
-- url     : https://prove2.me/submissions/aec465bf-42f9-493f-86fa-e3385689ed98

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_SmulSubMulLe
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Theorems.Thm_Formalism_IndefR_Fin_Four_integ_congr


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
    (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1) (Φ : W → ℂ) (a y : W) {μ : W} (hμ : μ ∈ L ⊓ Y) :
    coef χ L X Φ a (y + μ) = coef χ L X Φ a y := by
  unfold coef
  apply integ_congr hfinX
  intro t ht
  rw [hχr, hLL t ht μ hμ, mul_one]
end Formalism.IndefR.Fin.Four
