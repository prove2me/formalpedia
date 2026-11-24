-- Prove2me | solution 1 for Formalism.UG.P.spherical_chiDelta_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:05.317736+00:00
-- url     : https://prove2.me/submissions/cd65ba79-8185-4849-a525-e3fba68ecf73

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA
import Theorems.Thm_Formalism_UG_P_spherical_diag_mul
import Theorems.Thm_Formalism_UG_P_spherical_upper_inv
import Theorems.Thm_Formalism_UG_P_spherical_ordV_unit

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
theorem _root_.solution {n : ℕ} (α : Fin n → ℂ) (b : GL (Fin n) (v.adicCompletion F))
    (hb : (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id)
    (hk : b ∈ GLint (Fin n) (Ov F v)) : chiDelta F v α b = 1 := by
  obtain ⟨k, rfl⟩ := hk
  unfold chiDelta
  refine Finset.prod_eq_one fun i _ => ?_
  have hinv := spherical_upper_inv _ hb
  have hm : ((((bc (n := Fin n) (Ov F v).subtype) k)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i *
      (((bc (n := Fin n) (Ov F v).subtype) k : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i = 1 := by
    rw [← spherical_diag_mul _ _ hinv hb, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
  have h0 : ordV F v ((((bc (n := Fin n) (Ov F v).subtype) k : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) = 0 := by
    refine spherical_ordV_unit F v _ _ ?_ ?_ hm
    · simp only [bc, Units.coe_map]
      exact ((k : Matrix (Fin n) (Fin n) (Ov F v)) i i).2
    · rw [← map_inv (bc (n := Fin n) (Ov F v).subtype) k]
      simp only [bc, Units.coe_map]
      exact (((k⁻¹ : GL (Fin n) (Ov F v)) : Matrix (Fin n) (Fin n) (Ov F v)) i i).2
  rw [h0]; simp
end Formalism.UG.P
