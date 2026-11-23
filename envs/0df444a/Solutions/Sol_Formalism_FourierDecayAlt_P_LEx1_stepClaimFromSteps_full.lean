-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.stepClaimFromSteps_full
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:28:06.230677+00:00
-- url     : https://prove2.me/submissions/80f6fa36-0c5f-4210-bfd0-d6a35f9e13ed

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StepClaimFromStepsFull
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_dsMeas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx1_stepClaimFromSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution : StepClaimFromSteps := stepClaimFromSteps dsMeas
end Formalism.FourierDecayAlt.P.LEx1
