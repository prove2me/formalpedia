-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.admissible_atomic_form_one_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:46:21.854067+00:00
-- url     : https://prove2.me/submissions/b869d342-67a5-4c1c-9acc-234c24218fc2

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_VanishingOfL2Equivariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiscreteSeriesFormOneReduction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleAtomicFormOneReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_UnipotentHaarMeasurability_smooth_admissible_form_one_side

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
set_option maxHeartbeats 3200000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.ThreeDimData.AtFormAdmOneOfSteps := UnipotentHaarMeasurability.smooth_admissible_form_one_side
end Formalism.FourierDecayAlt.P
