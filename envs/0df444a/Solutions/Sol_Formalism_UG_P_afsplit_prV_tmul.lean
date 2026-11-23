-- Prove2me | solution 1 for Formalism.UG.P.afsplit_prV_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:35.967795+00:00
-- url     : https://prove2.me/submissions/db2b8b96-ed60-4837-b4d2-d146dadbd7bd

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 F)) (a : E) (b : 𝔸) :
    prV (E := E) w (a ⊗ₜ[F] b) = a ⊗ₜ[F] (b w) := rfl
end Formalism.UG.P
