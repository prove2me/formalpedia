-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.measurable_conjM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:00:57.512441+00:00
-- url     : https://prove2.me/submissions/2c368f71-e397-4739-8c8c-308d0631833d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HeisenbergLeviConjugationMeasure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x5
theorem _root_.solution {k r : ℕ} (a : Mat k r) : Measurable (conjM a) := by
  apply Continuous.measurable
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [conjM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop
end Formalism.FourierDecayAlt.P.B2x5
