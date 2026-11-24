-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.second_polynomial_third_of_parts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:22.084149+00:00
-- url     : https://prove2.me/submissions/d9f08367-fbeb-451a-ac03-0c8683a2b56b

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_p2cOfParts_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.LowerBlockNormalisedBoundFromComponents := by
  exact Formalism.FourierDecayAlt.P.SecondPolynomialClauses.p2cOfParts_ok
end Formalism.FourierDecayAlt.P
