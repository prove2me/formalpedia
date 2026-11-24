-- Prove2me | solution 1 for Formalism.UG.P.gLoc_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:21:47.193226+00:00
-- url     : https://prove2.me/submissions/9e2dc198-5aed-4ae9-b170-978f479f9323

import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Transport
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LocalAlgebraInertPrime
import Theorems.Thm_Formalism_UG_P_gLoc_hom_bij
import Theorems.Thm_Formalism_UG_P_gLoc_level

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
    (T : Subring A) (hT : ∀ x, x ∈ T ↔ e x ∈ intL L) (P : GL (Fin m) L)
    (hPO : P ∈ (bc (n := Fin m) (intL L).subtype).range)
    (hP : cT σL (P : Matrix (Fin m) (Fin m) L) * (P : Matrix (Fin m) (Fin m) L) = antiJ L m)
    (H Lv : Subgroup (GL (Fin m) A)) (hH : ∀ g, g ∈ H ↔ g ∈ UJ σA (1 : Matrix (Fin m) (Fin m) A))
    (hLv : ∀ g, g ∈ Lv ↔ g ∈ H ∧ g ∈ (bc (n := Fin m) T.subtype).range) :
    ∃ f : H ≃* GU σL m,
      (∀ x, ((f x : GU σL m) : GL (Fin m) L) = P⁻¹ * bc (e : A →+* L) x * P) ∧
      (Lv.subgroupOf H).map f.toMonoidHom = KU σL m := by
  refine ⟨MulEquiv.ofBijective (gLoc_hom σA σL e he P hP H hH) (gLoc_hom_bij σA σL e he P hP H hH),
    fun x => rfl, ?_⟩
  exact gLoc_level e T hT P hPO H Lv hLv _ (fun x => rfl)
end Formalism.UG.P
