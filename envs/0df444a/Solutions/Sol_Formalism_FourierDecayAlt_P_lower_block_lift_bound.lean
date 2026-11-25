-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lower_block_lift_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:54:48.276465+00:00
-- url     : https://prove2.me/submissions/1f25f35c-9d0b-4fef-ac97-41b232a45c5d

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialTheoremsAssembly
import Theorems.Thm_Formalism_FourierDecayAlt_P_lower_block_lift_bound_of_components
import Theorems.Thm_Formalism_FourierDecayAlt_P_second_polynomial_first_identity
import Theorems.Thm_Formalism_FourierDecayAlt_P_second_polynomial_third_of_parts
import Theorems.Thm_Formalism_FourierDecayAlt_P_unipotent_degree_three_of_clauses


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.LowerBlockLiftBound :=
  Formalism.FourierDecayAlt.P.lower_block_lift_bound_of_components Formalism.FourierDecayAlt.P.second_polynomial_first_identity Formalism.FourierDecayAlt.P.unipotent_degree_three_of_clauses
    Formalism.FourierDecayAlt.P.second_polynomial_third_of_parts
end Formalism.FourierDecayAlt.P
