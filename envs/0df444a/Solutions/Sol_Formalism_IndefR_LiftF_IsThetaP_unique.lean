-- Prove2me | solution 1 for Formalism.IndefR.LiftF.IsThetaP.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:05:45.658604+00:00
-- url     : https://prove2.me/submissions/decc125c-390b-4edb-a0fb-87d47074ddbc

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
namespace Formalism.IndefR.LiftF
namespace IsThetaP
theorem _root_.solution {ν : Measure H'} {𝓕 : Set H'} {th : G' → H' → S' → ℂ} {pt : Sinf' → S'}
    {io : TK →ₗ[ℂ] Tau →ₗ[ℂ] Sinf'} {A : Submodule ℂ (H' → Tau)}
    {thP thP' : A →ₗ[ℂ] (TK →ₗ[ℂ] (G' → ℂ))}
    (h : IsThetaP ν 𝓕 th pt io A thP) (h' : IsThetaP ν 𝓕 th pt io A thP') : thP = thP' := by
  refine LinearMap.ext fun f => LinearMap.ext fun e => funext fun g => ?_
  rw [h.eq, h'.eq]
end IsThetaP
end Formalism.IndefR.LiftF
