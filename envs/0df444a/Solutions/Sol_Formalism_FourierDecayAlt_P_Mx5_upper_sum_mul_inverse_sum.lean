-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.upper_sum_mul_inverse_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:10.633573+00:00
-- url     : https://prove2.me/submissions/7a8c92a5-7f79-4c24-8d0b-82c9b3c6c776

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_kap_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_diag_term
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_off_term

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx5
variable (P : Par)
namespace Formalism.FourierDecayAlt.P.Mx5
theorem _root_.solution (hN : ∀ l ∈ Icc 1 (P.k - 1), star (SS P l) * SS P l = kap P fun π => ((Nrm P l π : ℝ) : ℂ))
    (Y : ℂ) (hx : ∀ π, xC P π Y ≠ 0) :
    S12 P Y * ∑ j ∈ Icc 1 (P.k - 1), (kap P fun π => (Y + (rho P π j : ℂ))⁻¹) * SS P j =
      (kap P fun π => ∑ l ∈ Icc 1 (P.k - 1),
        xEx P {l} π Y * ((Nrm P l π : ℝ) : ℂ) * (Y + (rho P π l : ℂ) + 1)⁻¹) + S4 P Y := by
  unfold S12 S4
  rw [Finset.sum_mul, kap_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ hl, diag_term P (hN l hl) Y hl, add_right_inj]
  exact Finset.sum_congr rfl fun j hj =>
    off_term P Y hx (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
end Formalism.FourierDecayAlt.P.Mx5
