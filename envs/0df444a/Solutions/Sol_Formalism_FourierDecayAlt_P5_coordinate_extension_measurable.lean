-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.coordinate_extension_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:45:15.974732+00:00
-- url     : https://prove2.me/submissions/78777c39-6ec4-4144-aa1d-11fadac390ca

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
theorem _root_.solution (i : Fin (r + 1)) (c : Fin r → ℂ) : Measurable (coordinateExtension i c) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases h : i.val ≤ j.1.val
  · simp only [coordinateExtension, glue, dif_pos h]; exact measurable_pi_apply _
  · simp only [coordinateExtension, glue, dif_neg h]; exact measurable_const
end Formalism.FourierDecayAlt.P5
