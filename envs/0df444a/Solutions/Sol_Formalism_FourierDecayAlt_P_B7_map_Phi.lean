-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B7.map_Phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:38:40.294858+00:00
-- url     : https://prove2.me/submissions/ad7ac6ae-fc30-4382-bc41-cbb0ac5d3677

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_gqM_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_mem_good_set_or_weight_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_measurable_PhiM
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_meas_w
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_u_meas_inner

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) (hI : IntFormula D) :
    ((nuQ D).prod D.μSS).map (PhiM D) = D.μG := by
  have : SigmaFinite (nuQ D) := sfNu D
  refine Measure.ext_of_lintegral _ fun f hf => ?_
  have h1 : Measurable fun a : ((Fin r → ℂ) × ℂ) × SS k r => f (PhiM D a) := hf.comp (measurable_PhiM D)
  rw [lintegral_map hf (measurable_PhiM D), lintegral_prod _ h1.aemeasurable]
  unfold nuQ
  rw [lintegral_withDensity_eq_lintegral_mul _ (u_meas_w D) (u_meas_inner D hf), hI f hf]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_mem_good_set_or_weight_zero D] with q hq
  rcases hq with h | h
  · simp only [Pi.mul_apply, PhiM, gqM_eq D h]
    rfl
  · simp only [Pi.mul_apply, h, ENNReal.ofReal_zero, zero_mul]
end Formalism.FourierDecayAlt.P.B7
