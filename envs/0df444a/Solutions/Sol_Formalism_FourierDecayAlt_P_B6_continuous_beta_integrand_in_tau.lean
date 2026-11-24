-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.continuous_beta_integrand_in_tau
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:07.96552+00:00
-- url     : https://prove2.me/submissions/a7d2d4fd-a1ff-4944-849c-1cd14d3f4580

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_wt_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_phase_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_error_term_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_norm_exp_I_mul_real_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_integrable_pairing_times_phase_exp

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
theorem _root_.solution (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ} (hF : AdmW α c 2 2 F)
    (hF' : AdmW α c' 2 2 F') (p : SS k r) : Continuous (fun τ : ℝ × ℝ => Gt D F F' τ p) := by
  unfold Gt
  have hw : Continuous (fun τ : ℝ × ℝ => wt D τ p) :=
    (wt_continuous D).comp (f := fun τ : ℝ × ℝ => (τ, p)) (continuous_id.prodMk continuous_const)
  refine (Complex.continuous_ofReal.comp hw).mul ?_
  apply continuous_of_dominated (bound := fun t : ℝ × ℝ => ‖Et D F F' (p, t)‖)
  · intro τ
    exact (integrable_pairing_times_phase_exp H hF hF' τ p).aestronglyMeasurable
  · intro τ
    refine Filter.Eventually.of_forall fun t => ?_
    rw [norm_mul, norm_exp_I_mul_real_eq_one, mul_one]
  · exact (error_term_integrable H hF hF' p).norm
  · refine Filter.Eventually.of_forall fun t => ?_
    have hph : Continuous (fun τ : ℝ × ℝ => phase D τ p t) :=
      (phase_continuous D).comp (f := fun τ : ℝ × ℝ => ((τ, p), t))
        ((continuous_id.prodMk continuous_const).prodMk continuous_const)
    fun_prop
end Formalism.FourierDecayAlt.P.B6
