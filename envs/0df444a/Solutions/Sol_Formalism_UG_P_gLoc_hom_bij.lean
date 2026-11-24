-- Prove2me | solution 1 for Formalism.UG.P.gLoc_hom_bij
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:19.47288+00:00
-- url     : https://prove2.me/submissions/206cedfa-98ac-4edc-8562-faadfbdf032c

import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Transport
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LocalAlgebraInertPrime
import Theorems.Thm_Formalism_UG_P_gLoc_bc_symm
import Theorems.Thm_Formalism_UG_P_gLoc_bc_inj
import Theorems.Thm_Formalism_UG_P_gLoc_hom_apply

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
    (H : Subgroup (GL (Fin m) A)) (hH : ∀ g, g ∈ H ↔ g ∈ UJ σA (1 : Matrix (Fin m) (Fin m) A)) :
    Function.Bijective (gLoc_hom σA σL e he P hP H hH) := by
  constructor
  · intro x y hxy
    have h1 := congrArg (fun z : GU σL m => P * (z : GL (Fin m) L) * P⁻¹) hxy
    simp only [gLoc_hom_apply] at h1
    have h2 : bc (e : A →+* L) (x : GL (Fin m) A) = bc (e : A →+* L) (y : GL (Fin m) A) := by
      simpa [mul_assoc] using h1
    exact Subtype.ext (gLoc_bc_inj e h2)
  · intro y
    have hbg : bc (e : A →+* L) (bc (e.symm : L →+* A) (P * (y : GL (Fin m) L) * P⁻¹)) =
        P * (y : GL (Fin m) L) * P⁻¹ := gLoc_bc_symm e _
    have hmem : bc (e.symm : L →+* A) (P * (y : GL (Fin m) L) * P⁻¹) ∈ H := by
      rw [hH, gLoc_mem_one_iff σA σL e he, hbg, gLoc_conj_iff σL _ P hP]
      simpa [mul_assoc] using y.2
    refine ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    rw [gLoc_hom_apply, hbg]
    group
end Formalism.UG.P
