-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.coordinate_split_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:14:32.135051+00:00
-- url     : https://prove2.me/submissions/ed6f783b-2db0-40ee-a8f5-0feebe880e9f

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
theorem _root_.solution (l : Fin r) (a : Cf r l.castSucc) (j : {j : Fin r // l.succ.val ≤ j.val}) :
    (coordinateSplit l a).2 j = a ⟨j.1, by have := j.2; simp only [Fin.coe_castSucc, Fin.val_succ] at *; omega⟩ := by
  rfl
end Formalism.FourierDecayAlt.P5
