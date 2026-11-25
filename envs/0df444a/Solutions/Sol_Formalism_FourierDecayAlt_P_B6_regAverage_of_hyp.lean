-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.regAverage_of_hyp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:35:24.237588+00:00
-- url     : https://prove2.me/submissions/2b40a0d1-6978-4e94-8482-7b1f7515cd3a

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_B6_sigmaFinite__SS_1f0045a81b6a
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_weighted_of_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_of_weighted
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Bt_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_avg1
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_fourier_weighted_phase_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_second_integrand_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_integrand_slice_formula
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_integral_cutoff_product_eq_one

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
theorem _root_.solution (H : Hyp D Ξ α) (hJ : DilJac D) : RegAverage D α := by
  intro F F' ⟨c, hc⟩ ⟨c', hc'⟩ w₁ w₂ h₁ h₂
  have hF := admissible_weighted_of_bound hc
  have hF' := admissible_weighted_of_bound hc'
  have := sigmaFinite_μSS D
  refine ⟨fourier_weighted_phase_integrable H (admissible_of_weighted hF) (admissible_of_weighted hF') h₁ h₂, ?_⟩
  rw [avg1 H hF hF' h₁ h₂]
  have e1 : (∫ p : SS k r, (∫ t : ℝ × ℝ, regBracket D F F' p t.1 t.2 *
        (om w₁ (t.1 * lam k r D.z (Matrix.of p.1.2)) * om w₂ (-(t.2 * lam k r D.z' (Matrix.of p.2.2))))) ∂D.μSS) =
      ∫ p : SS k r, (∫ t : ℝ × ℝ, weightedPhaseJointIntegrand D F F' w₁ w₂ (p, t)) ∂D.μSS := by
    refine integral_congr_ae ?_
    filter_upwards [ae_inSS D] with p hp
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    show _ = weightedPhaseJointIntegrand D F F' w₁ w₂ (p, t)
    unfold weightedPhaseJointIntegrand
    rw [Bt_eq D F F' hp]
  rw [e1, integral_integral_swap (f := fun p t => weightedPhaseJointIntegrand D F F' w₁ w₂ (p, t))
    (second_integrand_integrable H hF hF' h₁ h₂)]
  simp only [integrand_slice_formula H hJ hF hF' h₁ h₂]
  rw [integral_mul_const, integral_cutoff_product_eq_one, one_mul]
  rfl
end Formalism.FourierDecayAlt.P.B6
