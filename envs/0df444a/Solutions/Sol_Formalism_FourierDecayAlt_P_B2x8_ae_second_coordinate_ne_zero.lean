-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.ae_second_coordinate_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:04:49.468618+00:00
-- url     : https://prove2.me/submissions/aa749759-73f8-48bf-95df-60797fd929bc

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
theorem _root_.solution : ∀ᵐ q : HPar k r' ∂(volume : Measure (HPar k r')), q.2 ≠ 0 := by
  rw [ae_iff, Measure.volume_eq_prod]
  have : {q : HPar k r' | ¬ q.2 ≠ 0} = Set.univ ×ˢ {0} := by ext q; simp
  rw [this, Measure.prod_prod, Real.volume_singleton, mul_zero]
end Formalism.FourierDecayAlt.P.B2x8
