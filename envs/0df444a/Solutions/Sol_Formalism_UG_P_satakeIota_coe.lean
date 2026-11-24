-- Prove2me | solution 1 for Formalism.UG.P.satakeIota_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:39:50.645871+00:00
-- url     : https://prove2.me/submissions/028a7ded-121b-4bce-a326-2cd5c9d59abe

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
theorem _root_.solution (r : 𝓞 F) :
    ((satakeIota v r : Ov F v) : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) r := by first | rfl | simp [satakeIota] | (unfold satakeIota Ov; done)
end Formalism.UG.P
