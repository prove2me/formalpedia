-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.level_weight_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:45:25.130878+00:00
-- url     : https://prove2.me/submissions/8c6b2be8-b8e2-4075-bc37-590a171035ab

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
theorem _root_.solution {β : Type} [MeasurableSpace β] (i : Fin (r + 1)) :
    Measurable (fun q : Cf r i × β => ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ)) := by
  fun_prop
end Formalism.FourierDecayAlt.P5
