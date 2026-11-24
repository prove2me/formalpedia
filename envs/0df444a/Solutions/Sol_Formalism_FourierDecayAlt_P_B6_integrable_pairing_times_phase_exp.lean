-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.integrable_pairing_times_phase_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:58:49.245904+00:00
-- url     : https://prove2.me/submissions/13b0b020-f615-4af6-b14c-4e0056453904

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_phase_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Et_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_error_term_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_norm_exp_I_mul_real_eq_one

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
theorem _root_.solution (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ}
    (hF : AdmW α c 2 2 F) (hF' : AdmW α c' 2 2 F') (τ : ℝ × ℝ) (p : SS k r) :
    Integrable (fun t : ℝ × ℝ => Et D F F' (p, t) * Complex.exp (Complex.I * (phase D τ p t : ℂ))) := by
  have hph : Continuous (fun t : ℝ × ℝ => phase D τ p t) :=
    (phase_continuous D).comp (f := fun t : ℝ × ℝ => ((τ, p), t)) (continuous_const.prodMk continuous_id)
  have hE := Et_continuous H hF hF' p
  have hcont : Continuous (fun t : ℝ × ℝ => Et D F F' (p, t) * Complex.exp (Complex.I * (phase D τ p t : ℂ))) := by
    fun_prop
  refine (error_term_integrable H hF hF' p).norm.mono' hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun t => ?_
  rw [norm_mul, norm_exp_I_mul_real_eq_one, mul_one]
end Formalism.FourierDecayAlt.P.B6
