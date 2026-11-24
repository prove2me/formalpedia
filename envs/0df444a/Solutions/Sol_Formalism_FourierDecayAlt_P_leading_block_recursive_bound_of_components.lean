-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.leading_block_recursive_bound_of_components
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:01:33.698392+00:00
-- url     : https://prove2.me/submissions/be5f76e7-e135-42b0-aed6-2d73e8b6c7c8

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialTheoremsAssembly
import Theorems.Thm_Formalism_FourierDecayAlt_P_PolynomialTheoremsAssembly_p3aOfParts_ok

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.LeadingBlockRecursiveBoundFromComponents := Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.p3aOfParts_ok
end Formalism.FourierDecayAlt.P
