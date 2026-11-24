-- Prove2me | solution 1 for Formalism.UG.P.cartan_unif_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:12.289391+00:00
-- url     : https://prove2.me/submissions/52aa1056-6dbb-405a-b388-94557041eb16

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open IsDedekindDomain NumberField
namespace Formalism.UG.P
theorem _root_.solution (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ : v.adicCompletion F) (h : IsUnifV F v ϖ) : Valued.v ϖ < 1 := by
  unfold IsUnifV at h
  rw [h]
  first
  | exact WithZero.coe_lt_coe.mpr (by decide)
  | exact WithZero.coe_lt_one.mpr (by decide)
  | decide
end Formalism.UG.P
