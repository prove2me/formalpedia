-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WeakApproximationGL.elim_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:49.804922+00:00
-- url     : https://prove2.me/submissions/267fcd8a-06e8-4d3c-b4c7-f42d83603992

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WeakApproximationGL
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G5
namespace Formalism.FourierDecayAlt.P.WeakApproximationGL
theorem _root_.solution (m : ℕ) :
    Function.Bijective (fun p : XY m => (Sum.elim p.1 p.2 : FinalTheorems m → ℂ)) :=
  (Equiv.sumArrowEquivProdArrow _ _ ℂ).symm.bijective
end Formalism.FourierDecayAlt.P.WeakApproximationGL
