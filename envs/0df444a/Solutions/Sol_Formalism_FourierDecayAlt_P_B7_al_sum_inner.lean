-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.al_sum_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:14:29.316618+00:00
-- url     : https://prove2.me/submissions/91d7e29c-fd63-4493-a8d1-befb799d7d7a

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B7
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
attribute [local instance] sfG sfW sfN sfW' sfSS properFD
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (A B : Wq →L[ℂ] Wp) {ι : Type*} [Fintype ι] (c : OrthonormalBasis ι ℂ Wq) :
    ∑ i, inner ℂ (A (c i)) (B (c i)) =
      LinearMap.trace ℂ Wq ((ContinuousLinearMap.adjoint A).comp B).toLinearMap := by
  rw [LinearMap.trace_eq_sum_inner _ c]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ContinuousLinearMap.adjoint_inner_right]
end Formalism.FourierDecayAlt.P.B7
