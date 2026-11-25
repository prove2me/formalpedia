-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.weight_last_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:15:47.228239+00:00
-- url     : https://prove2.me/submissions/329007de-4c62-43c6-98ca-f209f1fd7d17

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
theorem _root_.solution (a : Cf r (Fin.last r)) : (∏ l, ‖a l‖ ^ (-2 : ℤ)) = 1 := Finset.prod_of_isEmpty _
end Formalism.FourierDecayAlt.P5
