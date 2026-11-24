-- Prove2me | solution 1 for Formalism.UG.P.spherical_wd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:08:22.704877+00:00
-- url     : https://prove2.me/submissions/7c099b52-175f-4ba6-9fc6-324c712f5a4b

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Spherical
import Theorems.Thm_Formalism_UG_P_spherical_chiDelta_int
import Theorems.Thm_Formalism_UG_P_spherical_chiDelta_mul
import Theorems.Thm_Formalism_UG_P_spherical_upper_inv
import Theorems.Thm_Formalism_UG_P_spherical_upper_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.UG
open Formalism Formalism.UG Formalism.UG.P
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace Formalism.UG.P
theorem _root_.solution {n : ℕ} (α : Fin n → ℂ) (hα : ∀ i, α i ≠ 0) (b b' k k' : GL (Fin n) (v.adicCompletion F))
    (hb : (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id)
    (hb' : (b' : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id)
    (hk : k ∈ GLint (Fin n) (Ov F v)) (hk' : k' ∈ GLint (Fin n) (Ov F v)) (h : b * k = b' * k') :
    chiDelta F v α b = chiDelta F v α b' := by
  have hq : b'⁻¹ * b = k' * k⁻¹ := by
    calc b'⁻¹ * b = b'⁻¹ * (b * k) * k⁻¹ := by group
      _ = b'⁻¹ * (b' * k') * k⁻¹ := by rw [h]
      _ = k' * k⁻¹ := by group
  have hup : ((b'⁻¹ * b : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id :=
    spherical_upper_mul _ _ (spherical_upper_inv _ hb') hb
  have hint : b'⁻¹ * b ∈ GLint (Fin n) (Ov F v) := by
    rw [hq]
    exact Subgroup.mul_mem _ hk' (Subgroup.inv_mem _ hk)
  have hb_eq : b = b' * (b'⁻¹ * b) := by group
  rw [hb_eq, spherical_chiDelta_mul F v α hα b' _ hb' hup, spherical_chiDelta_int F v α _ hup hint, mul_one]
end Formalism.UG.P
