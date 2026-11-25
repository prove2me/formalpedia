-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.y_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:19:38.46381+00:00
-- url     : https://prove2.me/submissions/61780886-35f5-4ff7-8aff-10a6af267088

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_mem_good_set_or_weight_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_hsL_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_JM_eq

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
attribute [local instance] sfNu
namespace Formalism.FourierDecayAlt.P.B7
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (τ : ℝ × ℝ) :
    normSqTau D τ F = ∫⁻ q, ENNReal.ofReal (bcWeight k r (Tz k r D.z) (Tz k r D.z') q *
      ‖hsL (JM D F τ q)‖ ^ 2) := by
  unfold normSqTau jNormSq
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_good_set_or_weight_zero D] with q hq
  rcases hq with h | h
  · rw [JM_eq D F τ h, hsL_apply]
  · rw [h, zero_mul, zero_mul]
end Formalism.FourierDecayAlt.P.B7
