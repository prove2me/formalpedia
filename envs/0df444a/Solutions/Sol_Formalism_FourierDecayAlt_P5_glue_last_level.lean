-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.glue_last_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:14:33.024726+00:00
-- url     : https://prove2.me/submissions/972fe008-6d5f-447b-ada4-2a13a8001d2f

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
theorem _root_.solution (c : Fin r → ℂ) (a : Cf r (Fin.last r)) : glue (Fin.last r) c a = c := by
  funext j; have := j.isLt; simp only [glue, Fin.val_last]; rw [dif_neg (by omega)]
end Formalism.FourierDecayAlt.P5
