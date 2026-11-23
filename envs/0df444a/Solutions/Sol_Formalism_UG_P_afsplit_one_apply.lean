-- Prove2me | solution 1 for Formalism.UG.P.afsplit_one_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:01.55569+00:00
-- url     : https://prove2.me/submissions/dd204a64-17d3-40ed-a282-b543b441d0d4

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 F)) : (1 : 𝔸) w = 1 := rfl
end Formalism.UG.P
