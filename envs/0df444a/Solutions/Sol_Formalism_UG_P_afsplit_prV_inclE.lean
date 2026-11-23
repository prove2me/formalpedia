-- Prove2me | solution 1 for Formalism.UG.P.afsplit_prV_inclE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:58.999916+00:00
-- url     : https://prove2.me/submissions/4f3e4e50-4017-4541-ba47-30fcde1eb594

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitB

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
variable {F : Type} [Field F] [NumberField F] {E : Type} [CommRing E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
namespace Formalism.UG.P
theorem _root_.solution (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    prV (E := E) v (inclE (F := F) 𝔸 e) = inclE (F := F) (v.adicCompletion F) e := rfl
end Formalism.UG.P
