-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.coordinate_split_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:14:31.500112+00:00
-- url     : https://prove2.me/submissions/304e2ae3-1cb9-41e2-a22b-c7019d40422e

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
theorem _root_.solution (l : Fin r) (a : Cf r l.castSucc) : (coordinateSplit l a).1 = a ⟨l, by simp⟩ := by
  rfl
end Formalism.FourierDecayAlt.P5
