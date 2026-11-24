-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.dj_levM_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:04:49.374227+00:00
-- url     : https://prove2.me/submissions/13a23a2a-9933-4aeb-81b7-f5075e2bdeb4

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
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution (k r' : ℕ) : Continuous (levM k r') := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  unfold levM ιLev
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · by_cases hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1
    · simp only [hp, hq, dif_pos, and_self]
      exact (continuous_apply _).comp (continuous_apply _)
    · simp only [hp, hq, dif_pos, dif_neg, and_self, not_false_eq_true]
      exact continuous_const
  · simp only [hp, dif_neg, not_false_eq_true]
    exact continuous_const
end Formalism.FourierDecayAlt.P.B2x8
