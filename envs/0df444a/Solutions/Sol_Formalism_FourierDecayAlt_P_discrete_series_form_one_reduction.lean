-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.discrete_series_form_one_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:57:02.827518+00:00
-- url     : https://prove2.me/submissions/a817eadb-d524-44fa-b74c-2711c601c1a9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiscreteSeriesFormOneReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_discrete_form_one_side


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.ThreeDimData.DDFormOneOfSteps := DDSmoothness.discrete_form_one_side
end Formalism.FourierDecayAlt.P
