-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lower_block_lift_bound_of_components
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:54.362553+00:00
-- url     : https://prove2.me/submissions/8eb2e6a1-fe12-441c-9bad-56e8713fef5e

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialTheoremsAssembly
import Theorems.Thm_Formalism_FourierDecayAlt_P_PolynomialTheoremsAssembly_lower_block_lift_bound_reduction

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.LowerBlockLiftBoundFromComponents := Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.lower_block_lift_bound_reduction
end Formalism.FourierDecayAlt.P
