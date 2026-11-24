-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.w_hJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:32:42.79922+00:00
-- url     : https://prove2.me/submissions/2b603daf-8245-4885-8c50-7d65f126ef29

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_norm_xi
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_hsL_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_v_int_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_w_meas_xi

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (F : Mat k r → (Wq →L[ℂ] Wp)) (g : Mat k r)
    (hint : Integrable (fun p => rho D p F g) D.μSS) (τ : ℝ × ℝ) :
    hsVec (Jtau D τ F g) = ∫ p, xiTau D τ p • hsVec (rho D p F g) ∂D.μSS := by
  have hi : Integrable (fun p => xiTau D τ p • rho D p F g) D.μSS :=
    v_int_smul hint (w_meas_xi D τ) (norm_xi D τ)
  rw [← hsL_apply, Jtau, ← ContinuousLinearMap.integral_comp_comm _ hi]
  simp only [map_smul, hsL_apply]
end Formalism.FourierDecayAlt.P.B7
