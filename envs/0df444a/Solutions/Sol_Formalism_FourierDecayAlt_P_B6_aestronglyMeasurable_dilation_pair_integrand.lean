-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.aestronglyMeasurable_dilation_pair_integrand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:28:24.724149+00:00
-- url     : https://prove2.me/submissions/eb7f59f1-01af-4c75-a6a6-80b0e6188f11

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_measurableSet_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ph_continuousOn
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_test_function_fourier_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_first_eigenvalue_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuous_lambda_second_coordinate

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {Ξ : Mat k r → NNReal} {α : ℝ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : admitted α c F)
    (hF' : admitted α c' F') {w₁ w₂ : ℝ → ℝ} (h₁ : IsTest w₁) (h₂ : IsTest w₂) :
    AEStronglyMeasurable (fourierWeightedPhase D F F' w₁ w₂) D.μSS := by
  have hc : ContinuousOn (fourierWeightedPhase D F F' w₁ w₂) {p | D.inSS p} := by
    unfold fourierWeightedPhase
    refine ContinuousOn.mul (Continuous.continuousOn ?_) (ph_continuousOn H hF hF')
    exact ((test_function_fourier_continuous h₁).comp (first_eigenvalue_continuous D)).mul
      ((test_function_fourier_continuous h₂).comp (continuous_lambda_second_coordinate D).neg)
  have := hc.aestronglyMeasurable (μ := D.μSS) (measurableSet_inSS D)
  have hr : D.μSS.restrict {p | D.inSS p} = D.μSS := Measure.restrict_eq_self_of_ae_mem (ae_inSS D)
  rwa [hr] at this
end Formalism.FourierDecayAlt.P.B6
