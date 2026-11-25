-- Prove2me | solution 1 for Formalism.IndefR.LiftF.IsIo.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:05:27.386244+00:00
-- url     : https://prove2.me/submissions/f34178c6-cb9c-4557-bb82-321924e6b5f9

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
variable {G H S Sinf Ds Dt : Type*} [MeasurableSpace H]
  [AddCommGroup Sinf] [Module ℂ Sinf] [AddCommGroup Ds] [Module ℂ Ds] [AddCommGroup Dt] [Module ℂ Dt]
namespace Formalism.IndefR.LiftF
namespace IsIo
theorem _root_.solution {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {pt : Sinf → S}
    {T : Sinf →ₗ[ℂ] Ds →ₗ[ℂ] Dt} {CCs : Submodule ℂ (Ds →ₗ[ℂ] (H → ℂ))}
    {CCt : Submodule ℂ (Dt →ₗ[ℂ] (G → ℂ))} {io io' : CCs →ₗ[ℂ] CCt}
    (hT : ∀ u : CCt, (∀ φ v, (u : Dt →ₗ[ℂ] (G → ℂ)) (T φ v) = 0) → u = 0)
    (h : IsIo ν 𝓕 th pt T CCs CCt io) (h' : IsIo ν 𝓕 th pt T CCs CCt io') : io = io' := by
  refine LinearMap.ext fun F => sub_eq_zero.1 (hT _ fun φ v => ?_)
  funext g
  have h1 := h.eq F φ v g
  have h2 := h'.eq F φ v g
  simp only [Submodule.coe_sub, LinearMap.sub_apply, Pi.sub_apply, Pi.zero_apply]
  rw [← h1, ← h2, sub_self]
end IsIo
end Formalism.IndefR.LiftF
