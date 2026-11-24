-- Prove2me | solution 1 for Formalism.UG.P.gLoc_hom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:38:56.698842+00:00
-- url     : https://prove2.me/submissions/70cf9b9c-bc64-42b8-be23-3fddd0f6cdb9

import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Transport
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LocalAlgebraInertPrime

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
variable {A L : Type} [CommRing A] [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m : ℕ}
namespace Formalism.UG.P
theorem _root_.solution (σA : A →+* A) (σL : L →+* L) (e : A ≃+* L) (he : ∀ x, e (σA x) = σL (e x))
    (P : GL (Fin m) L)
    (hP : cT σL (P : Matrix (Fin m) (Fin m) L) * (P : Matrix (Fin m) (Fin m) L) = antiJ L m)
    (H : Subgroup (GL (Fin m) A)) (hH : ∀ g, g ∈ H ↔ g ∈ UJ σA (1 : Matrix (Fin m) (Fin m) A))
    (x : H) :
    ((gLoc_hom σA σL e he P hP H hH x : GU σL m) : GL (Fin m) L) =
      P⁻¹ * bc (e : A →+* L) (x : GL (Fin m) A) * P := rfl
end Formalism.UG.P
