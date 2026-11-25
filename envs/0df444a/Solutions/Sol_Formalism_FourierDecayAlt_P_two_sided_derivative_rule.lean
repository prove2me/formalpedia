-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.two_sided_derivative_rule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:57:52.193052+00:00
-- url     : https://prove2.me/submissions/4502d937-749e-46aa-bbeb-7b78be2d5e67

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ListSumSplittings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LeftToRightConversion
import Theorems.Thm_Formalism_FourierDecayAlt_P_LeftToRightConversion_twoSided

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.TwoSided := LeftToRightConversion.twoSided
end Formalism.FourierDecayAlt.P
