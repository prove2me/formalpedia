-- Prove2me | solution 1 for Formalism.IndefR.Fin.Four.IsSB.smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:42.724886+00:00
-- url     : https://prove2.me/submissions/6eac6f9e-aefd-493c-be6e-05b248cf674e

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourModel
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinitePlaces_FourExist

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
variable {L X : AddSubgroup W}
namespace Formalism.IndefR.Fin.Four
namespace IsSB
theorem _root_.solution {Φ : W → ℂ} (h : IsSB L X Φ) (c : ℂ) : IsSB L X (c • Φ) := by
  obtain ⟨hs, k, hk, hi, hl⟩ := h
  have hne : ∀ t, (c • Φ) t ≠ 0 → Φ t ≠ 0 := fun t ht h0 => ht (by simp [h0])
  exact ⟨fun t ht => hs t (hne t ht), k, hk, fun u hu t => by simp [hi u hu t],
    fun t ht => hl t (hne t ht)⟩
end IsSB
end Formalism.IndefR.Fin.Four
