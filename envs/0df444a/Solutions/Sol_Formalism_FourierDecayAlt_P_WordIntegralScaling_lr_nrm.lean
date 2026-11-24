-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordIntegralScaling.lr_nrm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:39:30.072832+00:00
-- url     : https://prove2.me/submissions/127afe0e-070d-498b-b133-45788e210562

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordIntegralScaling
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.WordIntegralScaling
theorem _root_.solution (v : List (Mat k r)) :
    (B4.lr [] v).map B4.nrm = B4.lr [] (v.map fun X => ((‖X‖⁻¹ : ℝ) : ℂ) • X) := by
  simp [B4.lr, B4.nrm, List.map_map, Function.comp_def]
end Formalism.FourierDecayAlt.P.WordIntegralScaling
