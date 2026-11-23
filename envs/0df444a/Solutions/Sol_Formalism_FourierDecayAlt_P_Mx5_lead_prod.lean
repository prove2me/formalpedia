-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx5.lead_prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:42.043528+00:00
-- url     : https://prove2.me/submissions/8e5d962e-4566-4db6-bfef-68a150b84a9f

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_Lead_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx5_lead_kap

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
theorem _root_.solution (s : Finset ℕ) :
    Lead s.card (1 : A P) fun Y => kap P fun π => ∏ i ∈ s, (Y + (rho P π i : ℂ)) := by
  have hm : ∀ π : Ty P, (∏ i ∈ s, (X + C (rho P π i : ℂ))).Monic := fun π =>
    Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _
  have hd : ∀ π : Ty P, (∏ i ∈ s, (X + C (rho P π i : ℂ))).natDegree = s.card := fun π => by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_add_C _]
    simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]
  have h := lead_kap P s.card (fun π => ∏ i ∈ s, (X + C (rho P π i : ℂ))) (fun _ => 1)
    (fun π => (hd π).le) (fun π => by rw [← hd π]; exact (hm π).coeff_natDegree)
  refine h.congr rfl (map_one (kap P)) fun Y => ?_
  congr 1
  funext π
  simp only [Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
end Formalism.FourierDecayAlt.P.Mx5
