-- Prove2me | solution 1 for Formalism.UG.P.spherical_chiDelta_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:52:57.263508+00:00
-- url     : https://prove2.me/submissions/3d21766c-6ebf-4b21-be08-9c670b1563b8

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SphericalA
import Theorems.Thm_Formalism_UG_P_spherical_diag_mul
import Theorems.Thm_Formalism_UG_P_spherical_diag_ne_zero
import Theorems.Thm_Formalism_UG_P_spherical_ordV_mul
import Theorems.Thm_Formalism_UG_P_spherical_qV_ne_zero

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
theorem _root_.solution {n : ℕ} (α : Fin n → ℂ) (hα : ∀ i, α i ≠ 0) (b c : GL (Fin n) (v.adicCompletion F))
    (hb : (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id)
    (hc : (c : Matrix (Fin n) (Fin n) (v.adicCompletion F)).BlockTriangular id) :
    chiDelta F v α (b * c) = chiDelta F v α b * chiDelta F v α c := by
  unfold chiDelta
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Units.val_mul, spherical_diag_mul _ _ hb hc i,
    spherical_ordV_mul F v _ _ (spherical_diag_ne_zero b hb i) (spherical_diag_ne_zero c hc i)]
  have hq := spherical_qV_ne_zero F v
  rw [zpow_add₀ (hα i)]
  push_cast
  rw [show (-((ordV F v ((b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ) +
      (ordV F v ((c : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ)) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2))
      = (-(ordV F v ((b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2))
        + (-(ordV F v ((c : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i i) : ℂ) * (((n : ℂ) - 1 - 2 * (i : ℂ)) / 2))
      by ring, Complex.cpow_add _ _ hq]
  ring
end Formalism.UG.P
