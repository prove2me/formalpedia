-- Prove2me | solution 1 for Formalism.IndefR.LiftF.IsLamP.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:05:40.585393+00:00
-- url     : https://prove2.me/submissions/cf5711fe-3182-4379-8554-948c641bd81e

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DatumF
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HasInfExpF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.IndefR Formalism.IndefR.LiftF
variable {G' H' S' Sinf' TK Tau : Type*} [MeasurableSpace H']
  [AddCommGroup Sinf'] [Module ℂ Sinf'] [AddCommGroup TK] [Module ℂ TK] [AddCommGroup Tau] [Module ℂ Tau]
variable {A Amb : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup Amb] [Module ℂ Amb]
namespace Formalism.IndefR.LiftF
namespace IsLamP
theorem _root_.solution {Sig : Type*} {thW : A →ₗ[ℂ] Amb} {adj : Amb →ₗ[ℂ] A} {part : Sig → Submodule ℂ Amb}
    {lam lam' : Sig → ℝ} (h : IsLamP thW adj part lam) (h' : IsLamP thW adj part lam') {σ : Sig}
    (hσ : part σ ≠ ⊥) : lam σ = lam' σ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  have h2 : ((lam σ : ℂ) - lam' σ) • x = 0 := by rw [sub_smul, ← h σ x hx, ← h' σ x hx, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · exact_mod_cast sub_eq_zero.1 h3
  · exact absurd h3 hx0
end IsLamP
end Formalism.IndefR.LiftF
