-- Prove2me | solution 1 for Formalism.UG.P.afsplit_sub_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:11:42.724605+00:00
-- url     : https://prove2.me/submissions/1afca364-7b3b-4bcc-b369-b81273bd2659

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
theorem _root_.solution (a b : 𝔸) (w : HeightOneSpectrum (𝓞 F)) : (a - b) w = a w - b w := rfl
end Formalism.UG.P
