-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.domination_scale_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:35:45.137073+00:00
-- url     : https://prove2.me/submissions/93d65715-59c9-4ec3-8391-1412a6bd4cd4

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensitySumsAndDomination
import Theorems.Thm_Formalism_FourierDecayAlt_P_DensitySumsAndDomination_domScaleTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexInnerProductSpace ComplexOrder ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.TC.DomScaleTop := DensitySumsAndDomination.domScaleTop
end Formalism.FourierDecayAlt.P
