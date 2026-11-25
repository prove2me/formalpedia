-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.recursion_hypothesis_scale_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:50:40.805648+00:00
-- url     : https://prove2.me/submissions/7f38b0db-2635-4470-adaa-ff727ec6a2cd

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensitySumsAndDomination
import Theorems.Thm_Formalism_FourierDecayAlt_P_DensitySumsAndDomination_recHypScaleTop

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
theorem _root_.solution : Formalism.FourierDecayAlt.TC.RecHypScaleTop := DensitySumsAndDomination.recHypScaleTop
end Formalism.FourierDecayAlt.P
