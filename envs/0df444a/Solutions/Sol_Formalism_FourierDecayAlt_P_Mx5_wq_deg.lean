-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.wq_deg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:59:07.210024+00:00
-- url     : https://prove2.me/submissions/75193b7b-4ef2-481e-aaf8-080549eeb3dd

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_coordinate_polynomial_monic
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_natDegree_x_polynomial
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_wNum_deg
import Theorems.Thm_Formalism_FourierDecayAlt_P_weight_exact


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
theorem _root_.solution (hP : P.OK) (π : Ty P) : (wNum P π /ₘ coordinatePolynomial P π).natDegree ≤ P.k + 1 ∧
    (wNum P π /ₘ coordinatePolynomial P π).coeff (P.k + 1) = -((P.T : ℂ) * P.T') := by
  have hk := hP.k_pos
  have hm := coordinate_polynomial_monic P π
  have hd := natDegree_x_polynomial P π
  obtain ⟨h1, h2⟩ := wNum_deg P hk π
  have h3 : (wNum P π /ₘ coordinatePolynomial P π).natDegree ≤ P.k + 1 := by
    rw [natDegree_divByMonic _ hm, hd]; omega
  refine ⟨h3, ?_⟩
  have h6 := coeff_mul_add_eq_of_natDegree_le hd.le h3
  rw [← weight_exact P hP π] at h6
  have h7 : (coordinatePolynomial P π).coeff (P.k - 1) = 1 := by
    have := hm.coeff_natDegree
    rwa [hd] at this
  have e : P.k - 1 + (P.k + 1) = 2 * P.k := by omega
  rw [h7, one_mul, e, h2] at h6
  exact h6.symm
end Formalism.FourierDecayAlt.P.Mx5
