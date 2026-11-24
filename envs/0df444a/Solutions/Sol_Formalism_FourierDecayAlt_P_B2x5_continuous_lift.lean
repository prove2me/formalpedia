-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x5.continuous_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:59:12.671782+00:00
-- url     : https://prove2.me/submissions/3f9507a8-0951-475d-b829-e13058062593

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
theorem _root_.solution (k r' : ℕ) : Continuous (liftVec k 1 r') := by
  apply continuous_pi
  intro p
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · simp only [liftVec, dif_pos hp]
    exact continuous_apply _
  · simp only [liftVec, dif_neg hp]
    exact continuous_const
end Formalism.FourierDecayAlt.P.B2x5
