-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.third_polynomial_second_of_first
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:04:40.565977+00:00
-- url     : https://prove2.me/submissions/edf915ef-6e46-4e00-a427-6f3d0eab2189

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_p3bOfA_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.LeadingBlockBoundFromRecursion := by
  exact Formalism.FourierDecayAlt.P.SecondPolynomialClauses.p3bOfA_ok
end Formalism.FourierDecayAlt.P
