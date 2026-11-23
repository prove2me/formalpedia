-- Prove2me | solution 1 for Formalism.UG.P.sigma_involution_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:14.852013+00:00
-- url     : https://prove2.me/submissions/758e3359-e7fd-4511-8508-56861169cea6

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsEasy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix NumberField
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution : Formalism.UG.CS.SigmaInvol := by
  intro F E _ _ _ _ _ σ hσ e
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  have h : ∀ x, τ (σ x) = starRingEnd ℂ (τ x) := fun x => by
    simpa using RingHom.congr_fun (hσ τ) x
  apply τ.injective
  rw [h, h, Complex.conj_conj]
end Formalism.UG.P
