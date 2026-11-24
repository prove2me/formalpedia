-- Prove2me | solution 1 for Formalism.UG.P.satake_ordV_unif
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:39:47.821108+00:00
-- url     : https://prove2.me/submissions/4fbb61cf-cbfd-407c-af2f-b4514cc5b559

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution {ϖ : v.adicCompletion F} (h : IsUnifV F v ϖ) : ordV F v ϖ = 1 := by
  unfold ordV IsUnifV at *
  have h0 : Valued.v ϖ ≠ 0 := by rw [h]; exact WithZero.coe_ne_zero
  rw [dif_neg h0]
  have e : ((WithZero.unzero h0 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [WithZero.coe_unzero, h]
  rw [WithZero.coe_injective e]
  simp
end Formalism.UG.P
