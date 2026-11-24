-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.measurable_lmulM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:47:22.166314+00:00
-- url     : https://prove2.me/submissions/cf464103-02a5-4daa-a336-084af86865d8

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
theorem _root_.solution {k r : ℕ} (a : Mat k r) : Measurable (lmulM a) := by
  apply Continuous.measurable
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop
end Formalism.FourierDecayAlt.P.B2x5
