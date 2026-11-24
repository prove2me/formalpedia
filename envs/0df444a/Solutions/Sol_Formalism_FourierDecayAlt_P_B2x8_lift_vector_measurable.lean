-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.lift_vector_measurable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:04:55.806562+00:00
-- url     : https://prove2.me/submissions/8020c3f6-6982-480f-8a7b-191012dee33d

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r' : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution : Measurable (fun y : Fin (2 * r' + k + 1) → ℂ => liftVec k 1 r' y) := by
  rw [measurable_pi_iff]
  intro p
  simp only [liftVec]
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const
end Formalism.FourierDecayAlt.P.B2x8
