-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.u_norm_hsInner_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:11:30.615907+00:00
-- url     : https://prove2.me/submissions/8de02b42-0d2e-468b-a4a2-a384bf674bd4

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_hsL_apply

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
theorem _root_.solution (A B : Wq →L[ℂ] Wp) :
    ‖hsInner A B‖ ≤ ‖hsL (Wp := Wp) (Wq := Wq)‖ ^ 2 * (‖A‖ * ‖B‖) := by
  unfold hsInner
  rw [← hsL_apply, ← hsL_apply]
  calc ‖inner ℂ (hsL B) (hsL A)‖ ≤ ‖hsL B‖ * ‖hsL A‖ := norm_inner_le_norm _ _
    _ ≤ (‖hsL (Wp := Wp) (Wq := Wq)‖ * ‖B‖) * (‖hsL (Wp := Wp) (Wq := Wq)‖ * ‖A‖) :=
        mul_le_mul (ContinuousLinearMap.le_opNorm _ B) (ContinuousLinearMap.le_opNorm _ A) (norm_nonneg _) (by positivity)
    _ = ‖hsL (Wp := Wp) (Wq := Wq)‖ ^ 2 * (‖A‖ * ‖B‖) := by ring
end Formalism.FourierDecayAlt.P.B7
