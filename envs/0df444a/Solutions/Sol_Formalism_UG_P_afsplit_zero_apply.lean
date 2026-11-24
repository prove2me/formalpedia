-- Prove2me | solution 1 for Formalism.UG.P.afsplit_zero_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:30:33.864374+00:00
-- url     : https://prove2.me/submissions/96fc3e0d-0b64-4963-8e7d-326782e11131

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F : Type} [Field F] [NumberField F]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
namespace Formalism.UG.P
theorem _root_.solution (w : HeightOneSpectrum (𝓞 F)) : (0 : 𝔸) w = 0 := rfl
end Formalism.UG.P
