-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.unipotent_degree_three_of_clauses
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:00.493068+00:00
-- url     : https://prove2.me/submissions/92c436cd-b301-4272-9cb1-65e1a3038efc

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_unipotent_degree_three_of_parts

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.UnnormalisedLiftBoundFromComponents := by
  exact Formalism.FourierDecayAlt.P.SecondPolynomialClauses.unipotent_degree_three_of_parts
end Formalism.FourierDecayAlt.P
