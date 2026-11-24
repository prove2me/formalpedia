-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.coef_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:12:33.146078+00:00
-- url     : https://prove2.me/submissions/e05ca03e-4647-405d-8d7c-62b306d4459b

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
theorem _root_.solution (Φ : W → ℂ) (hΦ : ∀ t, Φ t ≠ 0 → t ∈ X) {a : W} (ha : a ∉ X) (y : W) :
    coef χ L X Φ a y = 0 := by
  have h0 : ∀ t ∈ L ⊓ X, Φ (a + t) * (χ t y)⁻¹ = (fun _ : W => (0 : ℂ)) t := by
    intro t ht
    have hz : Φ (a + t) = 0 := by
      by_contra hne
      exact ha (by simpa using X.sub_mem (hΦ _ hne) (AddSubgroup.mem_inf.mp ht).2)
    simp [hz]
  unfold coef
  rw [integ_congr hfinX h0]
  unfold integ
  split_ifs with h
  · simp [avg]
  · rfl
end Formalism.IndefR.Fin.Four
