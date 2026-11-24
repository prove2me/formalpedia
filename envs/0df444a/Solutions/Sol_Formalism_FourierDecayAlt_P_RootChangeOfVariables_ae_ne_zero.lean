-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RootChangeOfVariables.ae_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T16:50:46.749457+00:00
-- url     : https://prove2.me/submissions/222db582-2e9c-40e1-bbc5-97989572947d

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourthWeightDensityOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JacobianAeNonzero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt MeasureTheory
open scoped ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.RootChangeOfVariables
namespace Formalism.FourierDecayAlt.P.RootChangeOfVariables
theorem _root_.solution : ∀ᵐ D : ℂ, D ∈ {D : ℂ | D ≠ 0} := by
  rw [ae_iff]
  have : {a : ℂ | ¬ a ∈ {D : ℂ | D ≠ 0}} = {0} := by ext a; simp
  rw [this, measure_singleton]
end Formalism.FourierDecayAlt.P.RootChangeOfVariables
