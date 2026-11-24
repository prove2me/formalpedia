-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.leading_block_lift_bound_of_components
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:33.432705+00:00
-- url     : https://prove2.me/submissions/9d45937e-ee77-4a0c-95e8-224d2d951d55

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialTheoremsAssembly
import Theorems.Thm_Formalism_FourierDecayAlt_P_PolynomialTheoremsAssembly_leading_block_lift_bound_reduction

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.LeadingBlockLiftBoundFromComponents := Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.leading_block_lift_bound_reduction
end Formalism.FourierDecayAlt.P
