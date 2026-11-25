-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.leading_block_lift_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:52:05.335879+00:00
-- url     : https://prove2.me/submissions/b1e702e1-8964-4b3a-bfa5-394b0c34e8a6

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialTheoremsAssembly
import Theorems.Thm_Formalism_FourierDecayAlt_P_leading_block_recursive_bound_of_components
import Theorems.Thm_Formalism_FourierDecayAlt_P_leading_block_lift_bound_of_components
import Theorems.Thm_Formalism_FourierDecayAlt_P_third_polynomial_second_of_first


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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.LeadingBlockLiftBound :=
  Formalism.FourierDecayAlt.P.leading_block_lift_bound_of_components Formalism.FourierDecayAlt.P.leading_block_recursive_bound_of_components Formalism.FourierDecayAlt.P.third_polynomial_second_of_first
end Formalism.FourierDecayAlt.P
