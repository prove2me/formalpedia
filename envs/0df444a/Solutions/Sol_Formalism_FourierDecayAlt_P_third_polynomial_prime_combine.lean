-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.third_polynomial_prime_combine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:35.190821+00:00
-- url     : https://prove2.me/submissions/61ee6fc8-244f-40b0-9042-0b51af09b259

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_third_polynomial_prime_combination

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.LeadingBlockSeveralPlacesBound := by
  exact Formalism.FourierDecayAlt.P.SecondPolynomialClauses.third_polynomial_prime_combination
end Formalism.FourierDecayAlt.P
