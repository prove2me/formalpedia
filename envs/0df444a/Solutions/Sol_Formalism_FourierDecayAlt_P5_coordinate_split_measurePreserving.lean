-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.coordinate_split_measurePreserving
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:13:00.193846+00:00
-- url     : https://prove2.me/submissions/3e92c4c3-9f45-42ed-951f-340a510b72d6

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaOfDensities
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsInnerAddSmulRight
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelIntegrandAestronglyMeasurable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
variable {r : ℕ}
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution (l : Fin r) : MeasurePreserving (coordinateSplit l) volume volume := by
  unfold coordinateSplit
  refine MeasurePreserving.trans (volume_preserving_piEquivPiSubtypeProd _ _) ?_
  exact MeasurePreserving.prod (measurePreserving_piUnique _)
    (volume_measurePreserving_piCongrLeft (fun _ => ℂ) (coordinateRestEquiv l))
end Formalism.FourierDecayAlt.P5
