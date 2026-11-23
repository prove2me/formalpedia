-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.rhoC_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:43:52.644462+00:00
-- url     : https://prove2.me/submissions/7599de3e-3346-48b8-af09-7bd44b4d29c6

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rho_inj


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset Polynomial
noncomputable section
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (P : Par) (hP : P.OK) (π : Ty P) : ∀ i ∈ Icc 1 (P.k - 1), ∀ j ∈ Icc 1 (P.k - 1),
    (rho P π i : ℂ) = (rho P π j : ℂ) → i = j := by
  intro i hi j hj h
  have h2 : rho P π i = rho P π j := by exact_mod_cast h
  rcases lt_trichotomy i j with h1 | h1 | h1
  · exact absurd h2 (ne_of_gt (Mx3.rho_inj P hP π i j hi hj h1))
  · exact h1
  · exact absurd h2 (ne_of_lt (Mx3.rho_inj P hP π j i hj hi h1))
end Formalism.FourierDecayAlt.P.Mx7
