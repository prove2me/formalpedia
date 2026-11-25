-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.regularised_pairing_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:43:57.95113+00:00
-- url     : https://prove2.me/submissions/2da3956e-3690-4e13-8ad7-0e173147afb2

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_constant_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_weighted_of_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_admissible_of_weighted
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_XX_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_xi_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_betaInfTau_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_Gt_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_weight_dominated_near_quadrant
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_half_quadrant_neighbourhood
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aestronglyMeasurable_beta_integrand
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuous_beta_integrand_in_tau

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
theorem _root_.solution (H : Hyp D Ξ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} (hcF : InCC α 4 F) (hcF' : InCC α 4 F') :
    ContinuousOn (fun τ => betaInfTau D τ F F') Quad := by
  obtain ⟨c, hc⟩ := hcF
  obtain ⟨c', hc'⟩ := hcF'
  have hF := admissible_weighted_of_bound hc
  have hF' := admissible_weighted_of_bound hc'
  have e : (fun τ => betaInfTau D τ F F') = fun τ => ∫ p, Gt D F F' τ p ∂D.μSS := by
    funext τ; exact betaInfTau_eq H hF hF' τ
  rw [e]
  intro τ₀ h₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨K, hK, hb⟩ := Gt_bound H
  obtain ⟨M, hM, hw⟩ := weight_dominated_near_quadrant D h₀
  have hcn := admissible_constant_nonneg (admissible_of_weighted hF)
  have hcn' := admissible_constant_nonneg (admissible_of_weighted hF')
  apply continuousAt_of_dominated (bound := fun p => M * (K * c * c') * (XX Ξ p * LL D p))
  · exact Filter.Eventually.of_forall fun τ => aestronglyMeasurable_beta_integrand H hF hF' τ
  · filter_upwards [half_quadrant_neighbourhood h₀] with τ hτ
    refine Filter.Eventually.of_forall fun p => ?_
    have hX := XX_nonneg Ξ p
    calc ‖Gt D F F' τ p‖ ≤ wt D τ p * (K * c * c' * XX Ξ p) := hb F F' c c' hF hF' τ p
      _ ≤ (M * LL D p) * (K * c * c' * XX Ξ p) := by
          apply mul_le_mul_of_nonneg_right (hw τ hτ.1 hτ.2 p)
          positivity
      _ = M * (K * c * c') * (XX Ξ p * LL D p) := by ring
  · exact (xi_integrable H).const_mul _
  · exact Filter.Eventually.of_forall fun p => (continuous_beta_integrand_in_tau H hF hF' p).continuousAt
end Formalism.FourierDecayAlt.P.B6
