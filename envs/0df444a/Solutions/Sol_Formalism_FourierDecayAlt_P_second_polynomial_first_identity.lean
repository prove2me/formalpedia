-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.second_polynomial_first_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:21.787823+00:00
-- url     : https://prove2.me/submissions/6c835dc0-0a6e-4187-b944-e8436f1cac0d

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_second_polynomial_first_clause

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
theorem _root_.solution : Formalism.FourierDecayAlt.PairingProductCorollary.PairingGramBound := by
  exact Formalism.FourierDecayAlt.P.SecondPolynomialClauses.second_polynomial_first_clause
end Formalism.FourierDecayAlt.P
